/*
Part of the EDG Compiler Project, under the Apache License v2.0 with LLVM
Exceptions.
See https://edgcpp.org/LICENSE.txt for license information.
SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
*/

/*
bend_gen_be.c -- A back end that translates the (unlowered) EDG IL of a small
C++ subset into Bend 2 source code, so that Bend laws and proofs can be
written about the C++ functions.

Supported subset (everything else is reported as "not supported"):

  types       bool -> Bool, unsigned int -> U32 (32-bit vector in Bend),
              plain structs whose fields have supported types -> Bend Data
              types with one constructor and one accessor def per field.
  functions   free functions defined in the translation unit, with by-value
              parameters and a non-void result; no overloading, no recursion.
  statements  blocks, local declarations with initializers, assignment to a
              local or a parameter (also to one field of a struct variable,
              and compound assignment), if / if-else, return.
  expressions variables, constants, struct aggregates T{...}, field selection
              a.f, calls, && || !, the bool ^ & | == != forms (that C++
              computes in int after promotion), u32 + - * / % & | ^ ~ << >>,
              u32 comparisons, and ?: .

Translation scheme:
  - C++ assignment to a local becomes a new Bend let of the same name (SSA by
    shadowing).  Each let is marked "+" (reusable): all supported types are
    Data in Bend.
  - An "if" becomes a call to a helper def "<function>.if<N>" that takes the
    condition and every live variable, and matches on the condition.  The
    statements after the "if" are copied into both branches, so the helper
    always produces the final result of the function.
  - u32 arithmetic is modulo 2^32 in both C++ and Bend.  C++ undefined
    behavior is not modeled: Bend gives a value for x / 0, x % 0 and for
    shifts by 32 or more.

The output goes to the file named by the EDG_BEND_OUT environment variable
(standard output if it is not set).  If any construct is not supported, the
messages go to standard error and the program exits with status 1.
*/

#include "fe_common.h"

#ifdef PCH_PRAGMA_GUARD
#pragma hdrstop
#endif /* ifdef PCH_PRAGMA_GUARD */

#include "il.h"
#include "types.h"
#include "const_ints.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

USING_NAMESPACE_EDG

namespace bend_gen {

/* ------------------------------------------------------------------------ */
/* Growable strings.                                                        */
/* ------------------------------------------------------------------------ */

struct Str {
  char   *p;
  size_t  n;
  size_t  cap;
};

/* Every string buffer is recorded here, so that back_end can free all of
   them at the end (the translation makes many short-lived strings). */
static char   **all_bufs     = NULL;
static size_t   n_all_bufs   = 0;
static size_t   cap_all_bufs = 0;

static void out_of_memory(void)
{
  fprintf(stderr, "bend back end: out of memory\n");
  exit(1);
}

/* Record that buffer "old" (NULL for a new buffer) is now "now". */
static void track_buf(char *old, char *now)
{
  if (old != NULL) {
    for (size_t i = n_all_bufs; i > 0; i--) {
      if (all_bufs[i - 1] == old) {
        all_bufs[i - 1] = now;
        return;
      }  /* if */
    }  /* for */
  }  /* if */
  if (n_all_bufs == cap_all_bufs) {
    size_t c = cap_all_bufs != 0 ? cap_all_bufs * 2 : 64;
    char **p = (char **)realloc(all_bufs, c * sizeof(char *));
    if (p == NULL) out_of_memory();
    all_bufs = p;
    cap_all_bufs = c;
  }  /* if */
  all_bufs[n_all_bufs++] = now;
}

static void free_all_bufs(void)
{
  for (size_t i = 0; i < n_all_bufs; i++) free(all_bufs[i]);
  free(all_bufs);
  all_bufs = NULL;
  n_all_bufs = cap_all_bufs = 0;
}

static void s_vadd(Str *s, const char *f, va_list ap)
{
  va_list ap2;
  va_copy(ap2, ap);
  int k = vsnprintf(NULL, 0, f, ap);
  size_t need = s->n + (size_t)k + 1;
  if (need > s->cap) {
    size_t c = s->cap != 0 ? s->cap : 256;
    while (c < need) c *= 2;
    char *p = (char *)realloc(s->p, c);
    if (p == NULL) out_of_memory();
    track_buf(s->p, p);
    s->p = p;
    s->cap = c;
  }  /* if */
  vsnprintf(s->p + s->n, (size_t)k + 1, f, ap2);
  va_end(ap2);
  s->n += (size_t)k;
}

static void s_add(Str *s, const char *f, ...)
{
  va_list ap;
  va_start(ap, f);
  s_vadd(s, f, ap);
  va_end(ap);
}

static const char *s_get(const Str *s)
{
  return s->p != NULL ? s->p : "";
}

/* Return a new heap string made from a printf format. */
static char *fmt(const char *f, ...)
{
  Str s = {NULL, 0, 0};
  va_list ap;
  va_start(ap, f);
  s_vadd(&s, f, ap);
  va_end(ap);
  if (s.p == NULL) {
    s.p = (char *)calloc(1, 1);
    if (s.p == NULL) out_of_memory();
    track_buf(NULL, s.p);
  }  /* if */
  return s.p;
}

static void indent(Str *out, int level)
{
  for (int i = 0; i < level; i++) s_add(out, "  ");
}

/* ------------------------------------------------------------------------ */
/* Diagnostics.                                                             */
/* ------------------------------------------------------------------------ */

static int         n_errors = 0;
static const char *cur_function = "";

static void not_supported(const a_source_position *pos, const char *what)
{
  a_const_char  *file_name = "?";
  a_const_char  *full_name = NULL;
  a_line_number  line = 0;
  a_boolean      at_end = FALSE;
  if (pos != NULL && pos->seq != 0) {
    (void)conv_seq_to_file_and_line(pos->seq, &file_name, &full_name, &line,
                                    &at_end);
  }  /* if */
  fprintf(stderr, "%s:%lu: bend back end: not supported in '%s': %s\n",
          file_name, (unsigned long)line, cur_function, what);
  n_errors++;
}

/* ------------------------------------------------------------------------ */
/* Names and types.                                                         */
/* ------------------------------------------------------------------------ */

static const char *const bend_reserved[] = {
  "match", "case", "def", "type", "law", "for", "exs", "where", "import",
  "as", "do", "return", "is", "Type", "Data", "Kind", "Quant", "True",
  "False", "Bool", "U32", "Nat", "F32", "List", "Base", "main", NULL
};

static const char *safe_name(const char *name)
{
  if (name == NULL) return "unnamed";
  for (int i = 0; bend_reserved[i] != NULL; i++) {
    if (strcmp(name, bend_reserved[i]) == 0) return fmt("%s_", name);
  }  /* for */
  return name;
}

enum a_bend_kind { bk_bool, bk_u32, bk_int, bk_struct, bk_other };

static a_bend_kind kind_of(a_type_ptr type)
{
  if (type == NULL) return bk_other;
  if (is_bool_type(type)) return bk_bool;
  a_type_ptr t = skip_typerefs(type);
  if (t->kind == tk_integer) {
    if (t->variant.integer.int_kind == ik_unsigned_int) return bk_u32;
    if (t->variant.integer.int_kind == ik_int) return bk_int;
    return bk_other;
  }  /* if */
  if (t->kind == tk_struct || t->kind == tk_class) return bk_struct;
  return bk_other;
}

static const char *struct_name(a_type_ptr type)
{
  return safe_name(skip_typerefs(type)->source_corresp.name);
}

static const char *bend_type(a_type_ptr type, const a_source_position *pos)
{
  switch (kind_of(type)) {
    case bk_bool:   return "Bool";
    case bk_u32:    return "U32";
    case bk_struct: return struct_name(type);
    case bk_int:
      not_supported(pos, "type 'int' (use bool or unsigned int)");
      return "?";
    case bk_other:
    default:
      not_supported(pos, "this type (only bool, unsigned int and structs)");
      return "?";
  }  /* switch */
}

static const char *var_name(a_variable_ptr var)
{
  return safe_name(var->source_corresp.name);
}

/* ------------------------------------------------------------------------ */
/* Live variables (the environment passed to "if" helpers).                 */
/* ------------------------------------------------------------------------ */

enum { MAX_VARS = 128 };

struct Env {
  const char *name[MAX_VARS];
  a_type_ptr  type[MAX_VARS];
  int         n;
};

static void env_bind(Env *env, const char *name, a_type_ptr type)
{
  for (int i = 0; i < env->n; i++) {
    if (strcmp(env->name[i], name) == 0) {
      env->type[i] = type;
      return;
    }  /* if */
  }  /* for */
  if (env->n < MAX_VARS) {
    env->name[env->n] = name;
    env->type[env->n] = type;
    env->n++;
  }  /* if */
}

/* ------------------------------------------------------------------------ */
/* Expressions.                                                             */
/* ------------------------------------------------------------------------ */

static char *tr_expr(an_expr_node_ptr e);
static char *tr_constant(a_constant_ptr cp, const a_source_position *pos);

static int constant_value(an_expr_node_ptr e, unsigned long long *value)
{
  if (e == NULL || e->kind != enk_constant) return 0;
  a_constant_ptr cp = e->variant.constant.ptr;
  if (cp == NULL || cp->kind != ck_integer) return 0;
  a_boolean ovflo = FALSE;
  *value = (unsigned long long)unsigned_value_of_integer_constant(cp, &ovflo);
  return 1;
}

/* An int-typed expression whose value comes from bool operands (C++ promotes
   bool to int for ^ & | == !=).  The result is a Bend Bool. */
static char *tr_boolish(an_expr_node_ptr e)
{
  unsigned long long v;
  if (constant_value(e, &v)) {
    if (v == 0) return fmt("False{}");
    if (v == 1) return fmt("True{}");
  }  /* if */
  if (e->kind == enk_operation) {
    an_expr_node_ptr a = e->variant.operation.operands;
    an_expr_node_ptr b = a != NULL ? a->next : NULL;
    switch (e->variant.operation.kind) {
      case eok_parens:
        return tr_boolish(a);
      case eok_cast:
        if (kind_of(a->type) == bk_bool) return tr_expr(a);
        break;
      case eok_xor:
        return fmt("Bool.xor(%s, %s)", tr_boolish(a), tr_boolish(b));
      case eok_and:
        return fmt("Bool.and(%s, %s)", tr_boolish(a), tr_boolish(b));
      case eok_or:
        return fmt("Bool.or(%s, %s)", tr_boolish(a), tr_boolish(b));
      case eok_ne:
        if (constant_value(b, &v) && v == 0) return tr_boolish(a);
        return fmt("Bool.xor(%s, %s)", tr_boolish(a), tr_boolish(b));
      case eok_eq:
        return fmt("Bool.not(Bool.xor(%s, %s))", tr_boolish(a),
                   tr_boolish(b));
      default:
        break;
    }  /* switch */
  }  /* if */
  not_supported(&e->position, "an 'int' expression that does not come from "
                              "bool values");
  return fmt("?");
}

/* Translate the shift count of << or >> (a Nat in Bend). */
static char *tr_shift_count(an_expr_node_ptr e)
{
  unsigned long long v;
  if (constant_value(e, &v)) return fmt("%llun", v);
  if (kind_of(e->type) == bk_u32) return fmt("U32.to_nat(%s)", tr_expr(e));
  if (e->kind == enk_operation && e->variant.operation.kind == eok_cast &&
      kind_of(e->variant.operation.operands->type) == bk_u32) {
    return fmt("U32.to_nat(%s)", tr_expr(e->variant.operation.operands));
  }  /* if */
  not_supported(&e->position, "a shift count that is not a constant or u32");
  return fmt("?");
}

static const char *u32_binary_op(an_expr_operator_kind op)
{
  switch (op) {
    case eok_add:       case eok_add_assign:       return "U32.add";
    case eok_subtract:  case eok_subtract_assign:  return "U32.sub";
    case eok_multiply:  case eok_multiply_assign:  return "U32.mul";
    case eok_divide:    case eok_divide_assign:    return "U32.div";
    case eok_remainder: case eok_remainder_assign: return "U32.mod";
    case eok_and:       case eok_and_assign:       return "U32.and";
    case eok_or:        case eok_or_assign:        return "U32.or";
    case eok_xor:       case eok_xor_assign:       return "U32.xor";
    case eok_eq: return "U32.is_eq";
    case eok_ne: return "U32.is_ne";
    case eok_lt: return "U32.is_lt";
    case eok_le: return "U32.is_le";
    case eok_gt: return "U32.is_gt";
    case eok_ge: return "U32.is_ge";
    default:     return NULL;
  }  /* switch */
}

static char *tr_call(an_expr_node_ptr e)
{
  an_expr_node_ptr f = e->variant.operation.operands;
  if (f->kind != enk_routine || f->variant.routine.ptr == NULL) {
    not_supported(&e->position, "a call that is not a direct call");
    return fmt("?");
  }  /* if */
  Str s = {NULL, 0, 0};
  s_add(&s, "%s(", safe_name(f->variant.routine.ptr->source_corresp.name));
  int first = 1;
  for (an_expr_node_ptr arg = f->next; arg != NULL; arg = arg->next) {
    s_add(&s, "%s%s", first ? "" : ", ", tr_expr(arg));
    first = 0;
  }  /* for */
  s_add(&s, ")");
  return s.p;
}

static char *tr_operation(an_expr_node_ptr e)
{
  an_expr_operator_kind op = e->variant.operation.kind;
  an_expr_node_ptr a = e->variant.operation.operands;
  an_expr_node_ptr b = a != NULL ? a->next : NULL;
  a_bend_kind rk = kind_of(e->type);

  switch (op) {
    case eok_parens:
      return tr_expr(a);
    case eok_cast:
    case eok_bool_cast: {
      a_bend_kind ak = kind_of(a->type);
      if (rk == ak && rk != bk_int) return tr_expr(a);
      if (rk == bk_bool) {
        if (ak == bk_int) return tr_boolish(a);
        if (ak == bk_u32) return fmt("Bool.not(U32.is_zero(%s))",
                                     tr_expr(a));
      } else if (rk == bk_u32) {
        unsigned long long v;
        if (ak == bk_bool) return fmt("Bool.to_u32(%s)", tr_expr(a));
        if (ak == bk_int && constant_value(a, &v)) {
          return fmt("%llu", v & 0xFFFFFFFFull);
        }  /* if */
      }  /* if */
      not_supported(&e->position, "this conversion (signed int values are "
                                  "not supported)");
      return fmt("?");
    }
    case eok_land:
      return fmt("Bool.and(%s, %s)", tr_expr(a), tr_expr(b));
    case eok_lor:
      return fmt("Bool.or(%s, %s)", tr_expr(a), tr_expr(b));
    case eok_not:
      return fmt("Bool.not(%s)", tr_expr(a));
    case eok_complement:
      if (rk == bk_u32) return fmt("U32.not(%s)", tr_expr(a));
      break;
    case eok_negate:
      if (rk == bk_u32) return fmt("U32.sub(0, %s)", tr_expr(a));
      break;
    case eok_shiftl:
      if (rk == bk_u32) {
        return fmt("U32.shln(%s, %s)", tr_expr(a), tr_shift_count(b));
      }  /* if */
      break;
    case eok_shiftr:
      if (rk == bk_u32) {
        return fmt("U32.shrn(%s, %s)", tr_expr(a), tr_shift_count(b));
      }  /* if */
      break;
    case eok_eq: case eok_ne: case eok_lt: case eok_le: case eok_gt:
    case eok_ge:
      if (kind_of(a->type) == bk_u32 && kind_of(b->type) == bk_u32) {
        return fmt("%s(%s, %s)", u32_binary_op(op), tr_expr(a), tr_expr(b));
      }  /* if */
      if (kind_of(a->type) == bk_int && kind_of(b->type) == bk_int &&
          (op == eok_eq || op == eok_ne)) {
        return tr_boolish(e);
      }  /* if */
      break;
    case eok_add: case eok_subtract: case eok_multiply: case eok_divide:
    case eok_remainder: case eok_and: case eok_or: case eok_xor:
      if (rk == bk_u32) {
        return fmt("%s(%s, %s)", u32_binary_op(op), tr_expr(a), tr_expr(b));
      }  /* if */
      if (rk == bk_int) return tr_boolish(e);
      break;
    case eok_dot_field: {
      a_field_ptr field = b->variant.field.ptr;
      return fmt("%s.%s(%s)", struct_name(a->type),
                 safe_name(field->source_corresp.name), tr_expr(a));
    }
    case eok_call:
      return tr_call(e);
    case eok_question: {
      an_expr_node_ptr c = b != NULL ? b->next : NULL;
      return fmt("Bool.pick(%s, %s, %s, %s)", bend_type(e->type, &e->position),
                 tr_expr(a), tr_expr(b), tr_expr(c));
    }
    default:
      break;
  }  /* switch */
  not_supported(&e->position, fmt("operator number %d with this operand type",
                                  (int)op));
  return fmt("?");
}

static char *tr_expr(an_expr_node_ptr e)
{
  if (e == NULL) {
    not_supported(NULL, "a missing expression");
    return fmt("?");
  }  /* if */
  switch (e->kind) {
    case enk_variable:
      return fmt("%s", var_name(e->variant.variable.ptr));
    case enk_constant:
      return tr_constant(e->variant.constant.ptr, &e->position);
    case enk_operation:
      return tr_operation(e);
    default:
      not_supported(&e->position, fmt("expression kind number %d",
                                      (int)e->kind));
      return fmt("?");
  }  /* switch */
}

static char *tr_dynamic_init(a_dynamic_init_ptr di,
                             const a_source_position *pos)
{
  switch (di->kind) {
    case dik_expression:
      return tr_expr(di->variant.expression);
    case dik_constant:
    case dik_nonconstant_aggregate:
      return tr_constant(di->variant.constant.ptr, pos);
    default:
      not_supported(pos, fmt("initialization kind number %d", (int)di->kind));
      return fmt("?");
  }  /* switch */
}

static int count_fields(a_type_ptr type)
{
  int n = 0;
  a_field_ptr f = skip_typerefs(type)->variant.class_struct_union.field_list;
  for (; f != NULL; f = f->next) n++;
  return n;
}

static char *tr_constant(a_constant_ptr cp, const a_source_position *pos)
{
  switch (cp->kind) {
    case ck_integer: {
      a_boolean ovflo = FALSE;
      unsigned long long v =
        (unsigned long long)unsigned_value_of_integer_constant(cp, &ovflo);
      switch (kind_of(cp->type)) {
        case bk_bool: return fmt(v != 0 ? "True{}" : "False{}");
        case bk_u32:  return fmt("%llu", v & 0xFFFFFFFFull);
        default:
          not_supported(pos, "an integer constant that is not bool or u32");
          return fmt("?");
      }  /* switch */
    }
    case ck_aggregate: {
      if (kind_of(cp->type) != bk_struct) break;
      Str s = {NULL, 0, 0};
      int n = 0;
      s_add(&s, "%s{", struct_name(cp->type));
      for (a_constant_ptr c = cp->variant.aggregate.first_constant;
           c != NULL; c = c->next) {
        s_add(&s, "%s%s", n == 0 ? "" : ", ", tr_constant(c, pos));
        n++;
      }  /* for */
      s_add(&s, "}");
      if (n != count_fields(cp->type)) {
        not_supported(pos, "a struct initializer that does not give every "
                           "field");
      }  /* if */
      return s.p;
    }
    case ck_dynamic_init:
      return tr_dynamic_init(cp->variant.dynamic_init.ptr, pos);
    default:
      break;
  }  /* switch */
  not_supported(pos, fmt("constant kind number %d", (int)cp->kind));
  return fmt("?");
}

/* ------------------------------------------------------------------------ */
/* Statements.                                                              */
/* ------------------------------------------------------------------------ */

/* The statements still to run after the current statement list ends. */
struct Cont {
  a_statement_ptr  stmts;
  const Cont      *up;
};

struct FnCtx {
  const char *name;         /* Bend name of the C++ function. */
  const char *result_type;  /* Bend result type. */
  int         n_helpers;
  Str         helpers;      /* Helper defs, written before the function. */
};

static void tr_seq(Str *out, int level, a_statement_ptr s, const Cont *k,
                   Env env, FnCtx *fc);

/* Translate an assignment statement into a Bend let.  Return FALSE if the
   expression is not an assignment. */
static a_boolean tr_assignment(Str *out, int level, an_expr_node_ptr e,
                               Env *env)
{
  if (e->kind != enk_operation) return FALSE;
  an_expr_operator_kind op = e->variant.operation.kind;
  an_expr_node_ptr lhs = e->variant.operation.operands;
  an_expr_node_ptr rhs = lhs != NULL ? lhs->next : NULL;
  char *value = NULL;

  /* Find the variable that is assigned, and the struct field if any. */
  an_expr_node_ptr target = lhs;
  a_field_ptr      field = NULL;
  if (target != NULL && target->kind == enk_operation &&
      target->variant.operation.kind == eok_dot_field) {
    an_expr_node_ptr obj = target->variant.operation.operands;
    field = obj->next->variant.field.ptr;
    target = obj;
  }  /* if */
  if (target == NULL || target->kind != enk_variable) {
    if (op == eok_assign) {
      not_supported(&e->position, "assignment to something that is not a "
                                  "variable or a field of a variable");
      return TRUE;
    }  /* if */
    return FALSE;
  }  /* if */
  a_variable_ptr var = target->variant.variable.ptr;
  const char *name = var_name(var);

  switch (op) {
    case eok_assign:
      value = tr_expr(rhs);
      break;
    case eok_add_assign: case eok_subtract_assign: case eok_multiply_assign:
    case eok_divide_assign: case eok_remainder_assign: case eok_and_assign:
    case eok_or_assign: case eok_xor_assign:
      if (kind_of(lhs->type) != bk_u32) {
        not_supported(&e->position, "compound assignment to a non-u32 value");
        return TRUE;
      }  /* if */
      value = fmt("%s(%s, %s)", u32_binary_op(op), tr_expr(lhs), tr_expr(rhs));
      break;
    case eok_shiftl_assign:
      value = fmt("U32.shln(%s, %s)", tr_expr(lhs), tr_shift_count(rhs));
      break;
    case eok_shiftr_assign:
      value = fmt("U32.shrn(%s, %s)", tr_expr(lhs), tr_shift_count(rhs));
      break;
    case eok_pre_incr: case eok_post_incr:
    case eok_pre_decr: case eok_post_decr:
      if (kind_of(lhs->type) != bk_u32) {
        not_supported(&e->position, "++ or -- on a non-u32 value");
        return TRUE;
      }  /* if */
      value = fmt("%s(%s, 1)",
                  (op == eok_pre_incr || op == eok_post_incr) ? "U32.add"
                                                               : "U32.sub",
                  tr_expr(lhs));
      break;
    default:
      return FALSE;
  }  /* switch */

  if (field != NULL) {
    /* Rebuild the struct with one new field value. */
    a_type_ptr st = var->type;
    Str s = {NULL, 0, 0};
    s_add(&s, "%s{", struct_name(st));
    int first = 1;
    for (a_field_ptr f = skip_typerefs(st)->variant.class_struct_union.
                                                                  field_list;
         f != NULL; f = f->next) {
      if (!first) s_add(&s, ", ");
      first = 0;
      if (f == field) {
        s_add(&s, "%s", value);
      } else {
        s_add(&s, "%s.%s(%s)", struct_name(st),
              safe_name(f->source_corresp.name), name);
      }  /* if */
    }  /* for */
    s_add(&s, "}");
    value = s.p;
  }  /* if */
  indent(out, level);
  s_add(out, "+%s = %s\n", name, value);
  env_bind(env, name, var->type);
  return TRUE;
}

static void tr_if(Str *out, int level, a_statement_ptr s, const Cont *k,
                  const Env *env, FnCtx *fc)
{
  int number = ++fc->n_helpers;
  const char *helper = fmt("%s.if%d", fc->name, number);
  Cont rest = {s->next, k};
  Str h = {NULL, 0, 0};

  /* The helper: match on the condition, run each branch, then the rest. */
  s_add(&h, "def %s(bend_c: Bool", helper);
  for (int i = 0; i < env->n; i++) {
    s_add(&h, ", +%s: %s", env->name[i], bend_type(env->type[i], &s->position));
  }  /* for */
  s_add(&h, ") -> %s:\n", fc->result_type);
  s_add(&h, "  match bend_c:\n");
  s_add(&h, "    case True{}:\n");
  tr_seq(&h, 3, s->variant.if_stmt.then_statement, &rest, *env, fc);
  s_add(&h, "    case False{}:\n");
  if (s->variant.if_stmt.else_statement != NULL) {
    tr_seq(&h, 3, s->variant.if_stmt.else_statement, &rest, *env, fc);
  } else {
    tr_seq(&h, 3, s->next, k, *env, fc);
  }  /* if */
  s_add(&h, "\n");
  s_add(&fc->helpers, "%s", s_get(&h));

  /* The call that replaces the "if" and everything after it. */
  indent(out, level);
  s_add(out, "%s(%s", helper, tr_expr(s->expr));
  for (int i = 0; i < env->n; i++) s_add(out, ", %s", env->name[i]);
  s_add(out, ")\n");
}

static void tr_seq(Str *out, int level, a_statement_ptr s, const Cont *k,
                   Env env, FnCtx *fc)
{
  for (; s != NULL; s = s->next) {
    switch (s->kind) {
      case stmk_block: {
        Cont rest = {s->next, k};
        tr_seq(out, level, s->variant.block.statements, &rest, env, fc);
        return;
      }
      case stmk_decl:
      case stmk_empty:
        break;
      case stmk_init: {
        a_dynamic_init_ptr di = s->variant.dynamic_init;
        if (di == NULL || di->variable == NULL) {
          not_supported(&s->position, "this initialization");
          break;
        }  /* if */
        const char *name = var_name(di->variable);
        (void)bend_type(di->variable->type, &s->position);
        indent(out, level);
        s_add(out, "+%s = %s\n", name, tr_dynamic_init(di, &s->position));
        env_bind(&env, name, di->variable->type);
        break;
      }
      case stmk_expr:
        if (!tr_assignment(out, level, s->expr, &env)) {
          not_supported(&s->position, "an expression statement that is not "
                                      "an assignment");
        }  /* if */
        break;
      case stmk_return: {
        char *value;
        if (s->expr != NULL) {
          value = tr_expr(s->expr);
        } else if (s->variant.return_dynamic_init != NULL) {
          value = tr_dynamic_init(s->variant.return_dynamic_init,
                                  &s->position);
        } else {
          not_supported(&s->position, "return with no value");
          value = fmt("?");
        }  /* if */
        indent(out, level);
        s_add(out, "%s\n", value);
        return;
      }
      case stmk_if:
        tr_if(out, level, s, k, &env, fc);
        return;
      default:
        not_supported(&s->position, fmt("statement kind number %d (loops, "
                                         "switch and goto are not supported)",
                                         (int)s->kind));
        return;
    }  /* switch */
  }  /* for */
  /* The list ended: continue with the enclosing statements. */
  if (k != NULL) {
    tr_seq(out, level, k->stmts, k->up, env, fc);
  } else {
    not_supported(NULL, "a path through the function with no return");
  }  /* if */
}

/* ------------------------------------------------------------------------ */
/* Declarations.                                                            */
/* ------------------------------------------------------------------------ */

static void gen_struct(Str *out, a_type_ptr type)
{
  const char *name = struct_name(type);
  a_field_ptr fields = type->variant.class_struct_union.field_list;
  cur_function = name;
  s_add(out, "type %s is Data:\n  %s{", name, name);
  for (a_field_ptr f = fields; f != NULL; f = f->next) {
    s_add(out, "%s%s: %s", f == fields ? "" : ", ",
          safe_name(f->source_corresp.name),
          bend_type(f->type, &f->source_corresp.decl_position));
  }  /* for */
  s_add(out, "}\n\n");
  /* One accessor def per field: S.f(x) is x.f in C++. */
  for (a_field_ptr f = fields; f != NULL; f = f->next) {
    const char *fname = safe_name(f->source_corresp.name);
    s_add(out, "def %s.%s(x: %s) -> %s:\n  match x:\n    case %s{",
          name, fname, name, bend_type(f->type, NULL), name);
    for (a_field_ptr g = fields; g != NULL; g = g->next) {
      s_add(out, "%s%s", g == fields ? "" : ", ",
            g == f ? fname : "_");
    }  /* for */
    s_add(out, "}:\n      %s\n\n", fname);
  }  /* for */
}

static void gen_routine(Str *out, a_routine_ptr rout)
{
  FnCtx fc;
  fc.name = safe_name(rout->source_corresp.name);
  fc.n_helpers = 0;
  fc.helpers.p = NULL;
  fc.helpers.n = fc.helpers.cap = 0;
  cur_function = fc.name;

  a_source_position *pos = &rout->source_corresp.decl_position;
  a_type_ptr rtype = skip_typerefs(rout->type)->variant.routine.return_type;
  fc.result_type = bend_type(rtype, pos);

  a_scope_ptr scope = scope_for_routine(rout);
  Env env;
  env.n = 0;
  Str head = {NULL, 0, 0};
  s_add(&head, "def %s(", fc.name);
  int first = 1;
  for (a_variable_ptr p = scope->variant.routine.parameters; p != NULL;
       p = p->next) {
    s_add(&head, "%s+%s: %s", first ? "" : ", ", var_name(p),
          bend_type(p->type, pos));
    env_bind(&env, var_name(p), p->type);
    first = 0;
  }  /* for */
  s_add(&head, ") -> %s:\n", fc.result_type);

  Str body = {NULL, 0, 0};
  tr_seq(&body, 1, scope->assoc_block, NULL, env, &fc);

  s_add(out, "%s", s_get(&fc.helpers));
  s_add(out, "# C++: %s\n", rout->source_corresp.name);
  s_add(out, "%s%s\n", s_get(&head), s_get(&body));
}

static a_boolean is_user_struct(a_type_ptr type)
{
  return (type->kind == tk_struct || type->kind == tk_class) &&
         type->source_corresp.name != NULL &&
         type->variant.class_struct_union.field_list != NULL;
}

}  /* namespace bend_gen */

using namespace bend_gen;

void back_end(void)
/*
Entry point called by the front end (BACK_END_SHOULD_BE_CALLED) after the
translation unit has been processed.  The IL is not lowered.
*/
{
  Str out = {NULL, 0, 0};
  a_scope_ptr file_scope = il_header.primary_scope;

  s_add(&out, "# Generated by EDG cpfe-bend from %s.\n",
        il_header.primary_source_file != NULL ?
          il_header.primary_source_file->file_name : "?");
  s_add(&out, "# Do not edit: run the translation again.\n\nimport Base\n\n");

  for (a_type_ptr t = file_scope->types; t != NULL; t = t->next) {
    if (is_user_struct(t)) gen_struct(&out, t);
  }  /* for */

  for (a_routine_ptr r = file_scope->routines; r != NULL; r = r->next) {
    if (r->function_def_number == NULL_function_def_number) continue;
    if (r->compiler_generated || r->source_corresp.name == NULL) continue;
    for (a_routine_ptr q = file_scope->routines; q != r; q = q->next) {
      if (q->function_def_number != NULL_function_def_number &&
          q->source_corresp.name != NULL &&
          strcmp(q->source_corresp.name, r->source_corresp.name) == 0) {
        cur_function = r->source_corresp.name;
        not_supported(&r->source_corresp.decl_position, "overloading");
      }  /* if */
    }  /* for */
    gen_routine(&out, r);
  }  /* for */

  const char *out_name = getenv("EDG_BEND_OUT");
  FILE *f = stdout;
  if (out_name != NULL && out_name[0] != '\0') {
    f = fopen(out_name, "w");
    if (f == NULL) {
      fprintf(stderr, "bend back end: cannot open %s\n", out_name);
      free_all_bufs();
      exit(1);
    }  /* if */
  }  /* if */
  fputs(s_get(&out), f);
  if (f != stdout) fclose(f);
  free_all_bufs();
  cur_function = "";
  if (n_errors != 0) {
    fprintf(stderr, "bend back end: %d construct(s) not supported; the Bend "
                    "output is not complete.\n", n_errors);
    exit(1);
  }  /* if */
}
