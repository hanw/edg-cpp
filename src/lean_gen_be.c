/*
Part of the EDG Compiler Project, under the Apache License v2.0 with LLVM
Exceptions.
See https://edgcpp.org/LICENSE.txt for license information.
SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
*/

/*
lean_gen_be.c -- A back end that translates the (unlowered) EDG IL of a small
C++ subset into Lean 4 source code, so that Lean theorems and proofs can be
written about the C++ functions.

Supported subset (everything else is reported as "not supported"):

  types       bool -> Bool, unsigned int -> U32 (= BitVec 32), plain structs
              whose fields have supported types -> Lean structures.
  functions   free functions defined in the translation unit, with by-value
              parameters and a non-void result; no overloading.  Recursion:
              a function may call itself as f(n - 1, ...) where n is its
              first parameter (unsigned int), n is never assigned, and n is
              tested against 0 before the call.  No mutual recursion.
  statements  blocks, local declarations with initializers, assignment to a
              local or a parameter (also to one field of a struct variable,
              and compound assignment), if / if-else, return.
  expressions variables, constants, struct aggregates T{...}, field selection
              a.f, calls, && || !, the bool ^ & | == != forms, u32 + - * / %
              & | ^ ~ << >>, u32 comparisons, and ?: .

Translation scheme:
  - All definitions go into "namespace C".  U32 is BitVec 32: + - * / % are
    modulo 2^32 (BitVec), & | ^ ~ are &&& ||| ^^^ ~~~, << and >> are <<< and
    >>> (by a Nat constant, or by a U32), < and <= are BitVec.ult and
    BitVec.ule (Bool results).  A u32 constant 5 is 5#32.
  - C++ assignment to a local becomes a new "let" of the same name.  An "if"
    becomes "bif c then ... else ...", and the statements after the "if" are
    copied into both branches.  "c ? x : y" becomes "bif c then x else y".
  - A recursive function f(n, ...) becomes
      def f.go (fuel : Nat) (n : U32) ... : T :=
        match fuel with
        | 0 => (body with each test of n against 0 decided: n is 0)
        | fuel' + 1 => (body with n not 0; f(n - 1, a...) is
                         f.go fuel' (n - 1) a...)
      def f (n : U32) ... : T := f.go n.toNat n ...
    Lean checks the structural recursion on fuel.  The translation is
    exact: fuel = n.toNat at the start, and when n != 0,
    (n - 1).toNat = n.toNat - 1 = fuel'.
  - C++ undefined behavior is not modeled: Lean gives a value for x / 0,
    x % 0 and for shifts by 32 or more.

Primitives: lean::Mem and lean::Ram (cpp-lean include/lean_mem.h) become the
structure Mem of a prelude: a function from U32 to U32, so a theorem about a
Mem parameter is about every array content.  lean::load(m, i) and
lean::ram_load(m, i) are Mem.load m i; lean::ram_store(m, i, v) is
Mem.store m i v, a new memory.

Laws in C++: a function named law_<name> that returns bool states "for all
values of its parameters, it returns true".  If EDG_LEAN_LAWS_OUT names a
file, each such function also becomes "def <name> : Prop := forall ...,
C.law_<name> ... = true" in namespace Laws in that file, which imports the
code file (EDG_LEAN_OUT, in the same directory, as a Lean module).  The
proofs prove these propositions.

The output goes to the file named by the EDG_LEAN_OUT environment variable
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

namespace lean_gen {

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
  fprintf(stderr, "lean back end: out of memory\n");
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
static int         quiet = 0;  /* Nonzero during a dry run: no messages. */

static void not_supported(const a_source_position *pos, const char *what)
{
  if (quiet) return;
  a_const_char  *file_name = "?";
  a_const_char  *full_name = NULL;
  a_line_number  line = 0;
  a_boolean      at_end = FALSE;
  if (pos != NULL && pos->seq != 0) {
    (void)conv_seq_to_file_and_line(pos->seq, &file_name, &full_name, &line,
                                    &at_end);
  }  /* if */
  fprintf(stderr, "%s:%lu: lean back end: not supported in '%s': %s\n",
          file_name, (unsigned long)line, cur_function, what);
  n_errors++;
}

/* ------------------------------------------------------------------------ */
/* Names and types.                                                         */
/* ------------------------------------------------------------------------ */

static const char *const lean_reserved[] = {
  "at", "by", "do", "fun", "if", "then", "else", "let", "in", "have", "show",
  "from", "match", "with", "where", "def", "theorem", "lemma", "structure",
  "namespace", "end", "open", "import", "instance", "class", "deriving",
  "mut", "return", "for", "true", "false", "Type", "Prop", "Sort",
  "inductive", "variable", "section", "universe", "axiom", "example",
  "abbrev", "opaque", "calc", "macro", "syntax", "local", "private",
  "protected", "partial", "unsafe", "noncomputable", "notation", "infix",
  "infixl", "infixr", "prefix", "postfix", "attribute", "termination_by",
  "decreasing_by", "try", "catch", "finally", "unless", "break", "continue",
  "nomatch", "nofun", "bif", "sorry", "suffices", "obtain", "U32", "Mem",
  "min", "max", "not", "and", "or", "xor", "id", "pure", "cond", "ite",
  "get", "load", "store", "toNat",
  "Nat", "Bool", "BitVec", "C", "Laws", "fuel", NULL
};

static const char *safe_name(const char *name)
{
  if (name == NULL) return "unnamed";
  for (int i = 0; lean_reserved[i] != NULL; i++) {
    if (strcmp(name, lean_reserved[i]) == 0) return fmt("%s_", name);
  }  /* for */
  return name;
}

/* Entities in namespace "lean" (include/lean_mem.h) are primitives with a
   fixed Lean meaning: lean::Mem is the type Mem of the prelude, and
   lean::load(m, i) is Mem.load m i.  Their C++ bodies are not translated. */
static int uses_mem = 0;

static a_boolean in_lean_ns(a_scope_ptr s)
{
  return s != NULL && s->kind == sck_namespace &&
         s->variant.assoc_namespace != NULL &&
         s->variant.assoc_namespace->source_corresp.name != NULL &&
         strcmp(s->variant.assoc_namespace->source_corresp.name, "lean") == 0;
}

static const char MEM_PRELUDE[] =
  "/-- lean::Mem and lean::Ram (include/lean_mem.h): an array of unsigned\n"
  "int.  Here it is any function from U32 to U32, so a theorem with a Mem\n"
  "parameter holds for every array content. -/\n"
  "structure Mem where\n"
  "  get : U32 -> U32\n\n"
  "/-- C++: lean::load(m, i), that is m.p[i] -/\n"
  "def Mem.load (m : Mem) (i : U32) : U32 := m.get i\n\n"
  "/-- C++: lean::ram_store(m, i, v): a new memory with v at i -/\n"
  "def Mem.store (m : Mem) (i v : U32) : Mem :=\n"
  "  Mem.mk (fun j => bif j == i then v else m.get j)\n\n";

enum a_lean_kind { bk_bool, bk_u32, bk_int, bk_struct, bk_other };

static a_lean_kind kind_of(a_type_ptr type)
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
  a_type_ptr t = skip_typerefs(type);
  if (in_lean_ns(t->source_corresp.parent_scope)) {
    if (t->source_corresp.name != NULL &&
        (strcmp(t->source_corresp.name, "Mem") == 0 ||
         strcmp(t->source_corresp.name, "Ram") == 0)) {
      uses_mem = 1;
      return "Mem";
    }  /* if */
    not_supported(NULL, "a type in namespace lean other than lean::Mem and lean::Ram");
    return "?";
  }  /* if */
  return safe_name(t->source_corresp.name);
}

static const char *lean_type(a_type_ptr type, const a_source_position *pos)
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
static char *tr_dynamic_init(a_dynamic_init_ptr di,
                             const a_source_position *pos);

static int constant_value(an_expr_node_ptr e, unsigned long long *value)
{
  if (e == NULL || e->kind != enk_constant) return 0;
  a_constant_ptr cp = e->variant.constant.ptr;
  if (cp == NULL || cp->kind != ck_integer) return 0;
  a_boolean ovflo = FALSE;
  *value = (unsigned long long)unsigned_value_of_integer_constant(cp, &ovflo);
  return 1;
}

/* ------------------------------------------------------------------------ */
/* Recursion.                                                               */
/*                                                                          */
/* A recursive function f(n, ...) must have an unsigned int first parameter */
/* n, must not assign n, must test n against 0 before each recursive call,  */
/* and each recursive call must be f(n - 1, ...).  See the header comment   */
/* for the Lean form (f.go with a Nat fuel that counts down).  Lean         */
/* checks the structural recursion on fuel.                                 */
/* ------------------------------------------------------------------------ */

enum a_zero_state { zs_unknown, zs_zero, zs_nonzero };

struct RecState {
  a_routine_ptr  self;        /* The function being translated. */
  a_boolean      dry_run;     /* TRUE while looking for recursive calls. */
  int            self_calls;  /* Found by the dry run. */
  a_variable_ptr n;           /* The parameter that counts down. */
  const char    *go_name;     /* "f.go". */
  a_zero_state   state;       /* Is n 0 in the case being translated? */
  int            in_helper;   /* Depth of "if" helper defs. */
};

static RecState rec = {NULL, FALSE, 0, NULL, NULL, zs_unknown, 0};

/* Functions already translated.  A function may call only these (and
   itself): Lean needs each def before its use, and has no mutual recursion. */
static a_routine_ptr *done_routines   = NULL;
static size_t         n_done_routines = 0;
static size_t         cap_done        = 0;

static void mark_done(a_routine_ptr r)
{
  if (n_done_routines == cap_done) {
    size_t c = cap_done != 0 ? cap_done * 2 : 32;
    a_routine_ptr *p = (a_routine_ptr *)realloc(done_routines,
                                                c * sizeof(a_routine_ptr));
    if (p == NULL) out_of_memory();
    done_routines = p;
    cap_done = c;
  }  /* if */
  done_routines[n_done_routines++] = r;
}

static a_boolean is_done(a_routine_ptr r)
{
  for (size_t i = 0; i < n_done_routines; i++) {
    if (done_routines[i] == r) return TRUE;
  }  /* for */
  return FALSE;
}

static void free_done_routines(void)
{
  free(done_routines);
  done_routines = NULL;
  n_done_routines = cap_done = 0;
}

/* Skip parentheses, and casts between 32-bit int and unsigned int (they
   keep "is zero" and "minus 1").  A cast to a narrower type (for example
   unsigned char) is not skipped: (unsigned char)n can be 0 when n is not. */
static an_expr_node_ptr strip(an_expr_node_ptr e)
{
  while (e != NULL && e->kind == enk_operation) {
    an_expr_operator_kind op = e->variant.operation.kind;
    an_expr_node_ptr a = e->variant.operation.operands;
    if (op == eok_parens) {
      e = a;
    } else if (op == eok_cast && a != NULL &&
               (kind_of(e->type) == bk_u32 || kind_of(e->type) == bk_int) &&
               (kind_of(a->type) == bk_u32 || kind_of(a->type) == bk_int)) {
      e = a;
    } else {
      break;
    }  /* if */
  }  /* while */
  return e;
}

static a_boolean is_rec_n(an_expr_node_ptr e)
{
  e = strip(e);
  return rec.n != NULL && e != NULL && e->kind == enk_variable &&
         e->variant.variable.ptr == rec.n;
}

static a_boolean is_const(an_expr_node_ptr e, unsigned long long v)
{
  unsigned long long value;
  return constant_value(strip(e), &value) && value == v;
}

/* If e compares n with 0 (n == 0, n != 0, n > 0, 0 < n, n <= 0, 0 >= n),
   return TRUE and set *true_when_zero to the value of e when n is 0. */
static a_boolean zero_test(an_expr_node_ptr e, a_boolean *true_when_zero)
{
  e = strip(e);
  if (rec.n == NULL || e == NULL || e->kind != enk_operation) return FALSE;
  an_expr_node_ptr a = e->variant.operation.operands;
  an_expr_node_ptr b = a != NULL ? a->next : NULL;
  if (b == NULL) return FALSE;
  a_boolean n_left = is_rec_n(a) && is_const(b, 0);
  a_boolean n_right = is_const(a, 0) && is_rec_n(b);
  if (!n_left && !n_right) return FALSE;
  switch (e->variant.operation.kind) {
    case eok_eq: *true_when_zero = TRUE;  return TRUE;
    case eok_ne: *true_when_zero = FALSE; return TRUE;
    case eok_gt: if (n_left)  { *true_when_zero = FALSE; return TRUE; } break;
    case eok_lt: if (n_right) { *true_when_zero = FALSE; return TRUE; } break;
    case eok_le: if (n_left)  { *true_when_zero = TRUE;  return TRUE; } break;
    case eok_ge: if (n_right) { *true_when_zero = TRUE;  return TRUE; } break;
    default: break;
  }  /* switch */
  return FALSE;
}

/* If e is a test of n against 0 and the case being translated fixes its
   value, return TRUE and set *value. */
static a_boolean known_zero_test(an_expr_node_ptr e, a_boolean *value)
{
  a_boolean true_when_zero;
  if (rec.state == zs_unknown || !zero_test(e, &true_when_zero)) return FALSE;
  *value = rec.state == zs_zero ? true_when_zero : !true_when_zero;
  return TRUE;
}

/* An int-typed expression whose value comes from bool operands (C++ promotes
   bool to int for ^ & | == !=).  The result is a Lean Bool. */
static char *tr_boolish(an_expr_node_ptr e)
{
  unsigned long long v;
  if (constant_value(e, &v)) {
    if (v == 0) return fmt("false");
    if (v == 1) return fmt("true");
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
        return fmt("(Bool.xor %s %s)", tr_boolish(a), tr_boolish(b));
      case eok_and:
        return fmt("(%s && %s)", tr_boolish(a), tr_boolish(b));
      case eok_or:
        return fmt("(%s || %s)", tr_boolish(a), tr_boolish(b));
      case eok_ne:
        if (constant_value(b, &v) && v == 0) return tr_boolish(a);
        return fmt("(Bool.xor %s %s)", tr_boolish(a), tr_boolish(b));
      case eok_eq:
        return fmt("(!(Bool.xor %s %s))", tr_boolish(a), tr_boolish(b));
      default:
        break;
    }  /* switch */
  }  /* if */
  not_supported(&e->position, "an 'int' expression that does not come from "
                              "bool values");
  return fmt("?");
}

/* Translate the shift count of << or >>: a Nat constant, or a U32 (BitVec
   shifts by a BitVec, which bv_decide can handle). */
static char *tr_shift_count(an_expr_node_ptr e)
{
  unsigned long long v;
  if (constant_value(e, &v)) return fmt("%llu", v);
  if (kind_of(e->type) == bk_u32) return tr_expr(e);
  if (e->kind == enk_operation && e->variant.operation.kind == eok_cast &&
      kind_of(e->variant.operation.operands->type) == bk_u32) {
    return tr_expr(e->variant.operation.operands);
  }  /* if */
  not_supported(&e->position, "a shift count that is not a constant or u32");
  return fmt("?");
}

/* The Lean form of a u32 binary operator: "(a OP b)" or "(OP a b)". */
static char *u32_binary(an_expr_operator_kind op, const char *a, const char *b)
{
  switch (op) {
    case eok_add:       case eok_add_assign:       return fmt("(%s + %s)", a, b);
    case eok_subtract:  case eok_subtract_assign:  return fmt("(%s - %s)", a, b);
    case eok_multiply:  case eok_multiply_assign:  return fmt("(%s * %s)", a, b);
    case eok_divide:    case eok_divide_assign:    return fmt("(%s / %s)", a, b);
    case eok_remainder: case eok_remainder_assign: return fmt("(%s %% %s)", a, b);
    case eok_and:       case eok_and_assign:       return fmt("(%s &&& %s)", a, b);
    case eok_or:        case eok_or_assign:        return fmt("(%s ||| %s)", a, b);
    case eok_xor:       case eok_xor_assign:       return fmt("(%s ^^^ %s)", a, b);
    case eok_shiftl:    case eok_shiftl_assign:    return fmt("(%s <<< %s)", a, b);
    case eok_shiftr:    case eok_shiftr_assign:    return fmt("(%s >>> %s)", a, b);
    case eok_eq: return fmt("(%s == %s)", a, b);
    case eok_ne: return fmt("(%s != %s)", a, b);
    case eok_lt: return fmt("(BitVec.ult %s %s)", a, b);
    case eok_le: return fmt("(BitVec.ule %s %s)", a, b);
    case eok_gt: return fmt("(BitVec.ult %s %s)", b, a);
    case eok_ge: return fmt("(BitVec.ule %s %s)", b, a);
    default:     return NULL;
  }  /* switch */
}

/* "(f a b)", or "f" for no arguments. */
static char *app(const char *f, an_expr_node_ptr args, const char *first)
{
  Str s = {NULL, 0, 0};
  int n = 0;
  s_add(&s, "(%s", f);
  if (first != NULL) {
    s_add(&s, " %s", first);
    n++;
  }  /* if */
  for (an_expr_node_ptr arg = args; arg != NULL; arg = arg->next) {
    s_add(&s, " %s", tr_expr(arg));
    n++;
  }  /* for */
  if (n == 0) return fmt("%s", f);
  s_add(&s, ")");
  return s.p;
}

static char *tr_call(an_expr_node_ptr e)
{
  an_expr_node_ptr f = e->variant.operation.operands;
  if (f->kind != enk_routine || f->variant.routine.ptr == NULL) {
    not_supported(&e->position, "a call that is not a direct call");
    return fmt("?");
  }  /* if */
  if (rec.self != NULL && f->variant.routine.ptr == rec.self) {
    /* A recursive call. */
    if (rec.dry_run) {
      rec.self_calls++;
      return fmt("?");
    }  /* if */
    an_expr_node_ptr first_arg = f->next;
    an_expr_node_ptr m = strip(first_arg);
    if (m == NULL || m->kind != enk_operation ||
        m->variant.operation.kind != eok_subtract ||
        !is_rec_n(m->variant.operation.operands) ||
        !is_const(m->variant.operation.operands->next, 1)) {
      not_supported(&e->position, "a recursive call whose first argument is "
                                  "not n - 1 (n: the first parameter)");
      return fmt("?");
    }  /* if */
    if (rec.state != zs_nonzero) {
      not_supported(&e->position, "a recursive call that can run when n is 0 "
                                  "(test n against 0 first: "
                                  "n == 0 ? base : f(n - 1, ...))");
      return fmt("?");
    }  /* if */
    return app(rec.go_name, first_arg->next,
               fmt("fuel' (%s - 1#32)", var_name(rec.n)));
  }  /* if */
  if (in_lean_ns(f->variant.routine.ptr->source_corresp.parent_scope)) {
    const char *nm = f->variant.routine.ptr->source_corresp.name;
    const char *bn = NULL;
    if (nm != NULL && (strcmp(nm, "load") == 0 || strcmp(nm, "ram_load") == 0)) {
      bn = "Mem.load";
    } else if (nm != NULL && strcmp(nm, "ram_store") == 0) {
      bn = "Mem.store";
    }  /* if */
    if (bn == NULL) {
      not_supported(&e->position, "a function in namespace lean other than "
                                  "load, ram_load and ram_store");
      return fmt("?");
    }  /* if */
    uses_mem = 1;
    return app(bn, f->next, NULL);
  }  /* if */
  if (!is_done(f->variant.routine.ptr)) {
    not_supported(&e->position, fmt("a call to '%s', which is not defined "
                                    "above this function (mutual recursion "
                                    "is not supported)",
                                    f->variant.routine.ptr->source_corresp.name));
  }  /* if */
  return app(safe_name(f->variant.routine.ptr->source_corresp.name), f->next,
             NULL);
}

static char *tr_operation(an_expr_node_ptr e)
{
  an_expr_operator_kind op = e->variant.operation.kind;
  an_expr_node_ptr a = e->variant.operation.operands;
  an_expr_node_ptr b = a != NULL ? a->next : NULL;
  a_lean_kind rk = kind_of(e->type);
  a_boolean known;

  /* In a recursive function, a test of n against 0 has a known value. */
  if (rk == bk_bool && known_zero_test(e, &known)) {
    return fmt(known ? "true" : "false");
  }  /* if */

  switch (op) {
    case eok_parens:
      return tr_expr(a);
    case eok_class_rvalue_adjust:
    case eok_lvalue_adjust:
      /* A change of cv-qualifiers only (for example "const S x = f();"):
         the value is the same. */
      if (rk == kind_of(a->type) &&
          (rk != bk_struct || skip_typerefs(e->type) == skip_typerefs(a->type))) {
        return tr_expr(a);
      }  /* if */
      break;
    case eok_cast:
    case eok_bool_cast: {
      a_lean_kind ak = kind_of(a->type);
      if (rk == ak && rk != bk_int) return tr_expr(a);
      if (rk == bk_bool) {
        if (ak == bk_int) return tr_boolish(a);
        if (ak == bk_u32) return fmt("(%s != 0#32)", tr_expr(a));
      } else if (rk == bk_u32) {
        unsigned long long v;
        if (ak == bk_bool) {
          return fmt("(bif %s then 1#32 else 0#32)", tr_expr(a));
        }  /* if */
        if (ak == bk_int && constant_value(a, &v)) {
          return fmt("%llu#32", v & 0xFFFFFFFFull);
        }  /* if */
      }  /* if */
      not_supported(&e->position, "this conversion (signed int values are "
                                  "not supported)");
      return fmt("?");
    }
    case eok_land:
      /* C++ does not run b when a is false. */
      if (known_zero_test(a, &known)) return known ? tr_expr(b) : fmt("false");
      return fmt("(%s && %s)", tr_expr(a), tr_expr(b));
    case eok_lor:
      /* C++ does not run b when a is true. */
      if (known_zero_test(a, &known)) return known ? fmt("true") : tr_expr(b);
      return fmt("(%s || %s)", tr_expr(a), tr_expr(b));
    case eok_not:
      return fmt("(!%s)", tr_expr(a));
    case eok_complement:
      if (rk == bk_u32) return fmt("(~~~%s)", tr_expr(a));
      break;
    case eok_negate:
      if (rk == bk_u32) return fmt("(0#32 - %s)", tr_expr(a));
      break;
    case eok_shiftl:
    case eok_shiftr:
      if (rk == bk_u32) return u32_binary(op, tr_expr(a), tr_shift_count(b));
      break;
    case eok_eq: case eok_ne: case eok_lt: case eok_le: case eok_gt:
    case eok_ge:
      if (kind_of(a->type) == bk_u32 && kind_of(b->type) == bk_u32) {
        return u32_binary(op, tr_expr(a), tr_expr(b));
      }  /* if */
      if (kind_of(a->type) == bk_int && kind_of(b->type) == bk_int &&
          (op == eok_eq || op == eok_ne)) {
        return tr_boolish(e);
      }  /* if */
      break;
    case eok_add: case eok_subtract: case eok_multiply: case eok_divide:
    case eok_remainder: case eok_and: case eok_or: case eok_xor:
      if (rk == bk_u32) return u32_binary(op, tr_expr(a), tr_expr(b));
      if (rk == bk_int) return tr_boolish(e);
      break;
    case eok_dot_field: {
      a_field_ptr field = b->variant.field.ptr;
      (void)struct_name(a->type);
      return fmt("%s.%s", tr_expr(a), safe_name(field->source_corresp.name));
    }
    case eok_call:
      return tr_call(e);
    case eok_question: {
      an_expr_node_ptr c = b != NULL ? b->next : NULL;
      if (known_zero_test(a, &known)) {
        /* Only the branch that runs is translated. */
        return tr_expr(known ? b : c);
      }  /* if */
      (void)lean_type(e->type, &e->position);
      return fmt("(bif %s then %s else %s)", tr_expr(a), tr_expr(b),
                 tr_expr(c));
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
      /* A bool call of a constexpr function that the front end has
         evaluated (for example a law with no parameters): translate the
         call, not its value, so that Lean does the evaluation and checks
         it (also for u32 and struct results). */
      if (e->variant.constant.ptr->is_result_of_constexpr_call &&
          e->variant.constant.ptr->expr != NULL) {
        return tr_expr(e->variant.constant.ptr->expr);
      }  /* if */
      return tr_constant(e->variant.constant.ptr, &e->position);
    case enk_operation:
      return tr_operation(e);
    case enk_temp_init:
      /* A temporary, for example the result of f() in "f().x": its value
         is the value of its initializer. */
      if (e->variant.init.dynamic_init != NULL) {
        return tr_dynamic_init(e->variant.init.dynamic_init, &e->position);
      }  /* if */
      break;
    default:
      break;
  }  /* switch */
  not_supported(&e->position, fmt("expression kind number %d", (int)e->kind));
  return fmt("?");
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
        case bk_bool: return fmt(v != 0 ? "true" : "false");
        case bk_u32:  return fmt("%llu#32", v & 0xFFFFFFFFull);
        default:
          not_supported(pos, "an integer constant that is not bool or u32");
          return fmt("?");
      }  /* switch */
    }
    case ck_aggregate: {
      if (kind_of(cp->type) != bk_struct) break;
      Str s = {NULL, 0, 0};
      int n = 0;
      s_add(&s, "(%s.mk", struct_name(cp->type));
      for (a_constant_ptr c = cp->variant.aggregate.first_constant;
           c != NULL; c = c->next) {
        s_add(&s, " %s", tr_constant(c, pos));
        n++;
      }  /* for */
      s_add(&s, ")");
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

static void tr_seq(Str *out, int level, a_statement_ptr s, const Cont *k,
                   Env env);

/* Write "let name : T := value".  The type is always given. */
static void emit_let(Str *out, const char *name, const char *value,
                     a_type_ptr type)
{
  s_add(out, "let %s : %s := %s\n", name, lean_type(type, NULL), value);
}

/* Translate an assignment statement into a Lean let.  Return FALSE if the
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
  if (rec.n != NULL && var == rec.n) {
    not_supported(&e->position, "assignment to n, the first parameter of a "
                                "recursive function");
    return TRUE;
  }  /* if */

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
      value = u32_binary(op, tr_expr(lhs), tr_expr(rhs));
      break;
    case eok_shiftl_assign:
    case eok_shiftr_assign:
      value = u32_binary(op, tr_expr(lhs), tr_shift_count(rhs));
      break;
    case eok_pre_incr: case eok_post_incr:
    case eok_pre_decr: case eok_post_decr:
      if (kind_of(lhs->type) != bk_u32) {
        not_supported(&e->position, "++ or -- on a non-u32 value");
        return TRUE;
      }  /* if */
      value = fmt("(%s %s 1#32)", tr_expr(lhs),
                  (op == eok_pre_incr || op == eok_post_incr) ? "+" : "-");
      break;
    default:
      return FALSE;
  }  /* switch */

  if (field != NULL) {
    /* A new struct with one new field value. */
    value = fmt("{ %s with %s := %s }", name,
                safe_name(field->source_corresp.name), value);
  }  /* if */
  indent(out, level);
  emit_let(out, name, value, var->type);
  env_bind(env, name, var->type);
  return TRUE;
}

static void tr_if(Str *out, int level, a_statement_ptr s, const Cont *k,
                  const Env *env)
{
  a_boolean known;
  Cont rest = {s->next, k};
  if (known_zero_test(s->expr, &known)) {
    /* A test of n against 0 in a recursive function: only the branch that
       runs is translated. */
    if (known) {
      tr_seq(out, level, s->variant.if_stmt.then_statement, &rest, *env);
    } else if (s->variant.if_stmt.else_statement != NULL) {
      tr_seq(out, level, s->variant.if_stmt.else_statement, &rest, *env);
    } else {
      tr_seq(out, level, s->next, k, *env);
    }  /* if */
    return;
  }  /* if */
  /* Each branch continues with the statements after the "if". */
  indent(out, level);
  s_add(out, "bif %s then\n", tr_expr(s->expr));
  tr_seq(out, level + 1, s->variant.if_stmt.then_statement, &rest, *env);
  indent(out, level);
  s_add(out, "else\n");
  if (s->variant.if_stmt.else_statement != NULL) {
    tr_seq(out, level + 1, s->variant.if_stmt.else_statement, &rest, *env);
  } else {
    tr_seq(out, level + 1, s->next, k, *env);
  }  /* if */
}

static void tr_seq(Str *out, int level, a_statement_ptr s, const Cont *k,
                   Env env)
{
  for (; s != NULL; s = s->next) {
    switch (s->kind) {
      case stmk_block: {
        Cont rest = {s->next, k};
        tr_seq(out, level, s->variant.block.statements, &rest, env);
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
        (void)lean_type(di->variable->type, &s->position);
        indent(out, level);
        emit_let(out, name, tr_dynamic_init(di, &s->position),
                 di->variable->type);
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
        tr_if(out, level, s, k, &env);
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
    tr_seq(out, level, k->stmts, k->up, env);
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
  s_add(out, "/-- C++: struct %s -/\nstructure %s where\n",
        type->source_corresp.name, name);
  for (a_field_ptr f = fields; f != NULL; f = f->next) {
    s_add(out, "  %s : %s\n", safe_name(f->source_corresp.name),
          lean_type(f->type, &f->source_corresp.decl_position));
  }  /* for */
  s_add(out, "\n");
}

static void gen_routine(Str *out, a_routine_ptr rout)
{
  const char *name = safe_name(rout->source_corresp.name);
  cur_function = name;

  a_source_position *pos = &rout->source_corresp.decl_position;
  a_type_ptr rtype = skip_typerefs(rout->type)->variant.routine.return_type;
  const char *result_type = lean_type(rtype, pos);

  a_scope_ptr scope = scope_for_routine(rout);
  a_variable_ptr params = scope->variant.routine.parameters;
  Env env;
  env.n = 0;
  Str plist = {NULL, 0, 0};   /* " (a : T) (b : U)" */
  Str alist = {NULL, 0, 0};   /* " a b" */
  for (a_variable_ptr p = params; p != NULL; p = p->next) {
    s_add(&plist, " (%s : %s)", var_name(p), lean_type(p->type, pos));
    s_add(&alist, " %s", var_name(p));
    env_bind(&env, var_name(p), p->type);
  }  /* for */

  /* Dry run: does the function call itself? */
  rec.self = rout;
  rec.dry_run = TRUE;
  rec.self_calls = 0;
  {
    Str scratch = {NULL, 0, 0};
    quiet++;
    tr_seq(&scratch, 1, scope->assoc_block, NULL, env);
    quiet--;
  }
  rec.dry_run = FALSE;

  if (rec.self_calls == 0) {
    rec.self = NULL;
    Str body = {NULL, 0, 0};
    tr_seq(&body, 1, scope->assoc_block, NULL, env);
    s_add(out, "/-- C++: %s -/\n", rout->source_corresp.name);
    s_add(out, "def %s%s : %s :=\n%s\n", name, s_get(&plist), result_type,
          s_get(&body));
    return;
  }  /* if */

  /* A recursive function: count down on the first parameter. */
  if (params == NULL || kind_of(params->type) != bk_u32) {
    not_supported(pos, "a recursive function whose first parameter is not "
                       "unsigned int");
    rec.self = NULL;
    return;
  }  /* if */
  rec.n = params;
  rec.go_name = fmt("%s.go", name);
  Str case0 = {NULL, 0, 0};
  Str case1 = {NULL, 0, 0};
  rec.state = zs_zero;
  tr_seq(&case0, 2, scope->assoc_block, NULL, env);
  rec.state = zs_nonzero;
  tr_seq(&case1, 2, scope->assoc_block, NULL, env);
  rec.state = zs_unknown;

  s_add(out, "/-- C++: %s (recursive: fuel counts down with %s) -/\n",
        rout->source_corresp.name, var_name(params));
  s_add(out, "def %s (fuel : Nat)%s : %s :=\n", rec.go_name, s_get(&plist),
        result_type);
  s_add(out, "  match fuel with\n  | 0 =>\n%s  | fuel' + 1 =>\n%s\n",
        s_get(&case0), s_get(&case1));
  s_add(out, "/-- C++: %s -/\n", rout->source_corresp.name);
  s_add(out, "def %s%s : %s :=\n  %s %s.toNat%s\n\n", name, s_get(&plist),
        result_type, rec.go_name, var_name(params), s_get(&alist));
  rec.self = NULL;
  rec.n = NULL;
  rec.go_name = NULL;
}

/* ------------------------------------------------------------------------ */
/* Laws.                                                                    */
/*                                                                          */
/* A function whose name starts with "law_" and that returns bool is a law: */
/* "for all values of the parameters, the function returns true".  It is   */
/* translated like any other function, and it also gives                    */
/*                                                                          */
/*   def <name without law_> : Prop :=                                      */
/*     forall (a : C.T) ..., C.law_<name> a ... = true                      */
/*                                                                          */
/* in namespace Laws of the laws file (EDG_LEAN_LAWS_OUT), which imports    */
/* the code module.                                                         */
/* ------------------------------------------------------------------------ */

static const char LAW_PREFIX[] = "law_";

static a_boolean is_law(a_routine_ptr rout)
{
  const char *name = rout->source_corresp.name;
  return name != NULL &&
         strncmp(name, LAW_PREFIX, sizeof(LAW_PREFIX) - 1) == 0 &&
         name[sizeof(LAW_PREFIX) - 1] != '\0';
}

static void gen_law(Str *laws, a_routine_ptr rout)
{
  const char *name = safe_name(rout->source_corresp.name);
  a_source_position *pos = &rout->source_corresp.decl_position;
  cur_function = name;
  a_type_ptr rtype = skip_typerefs(rout->type)->variant.routine.return_type;
  if (kind_of(rtype) != bk_bool) {
    not_supported(pos, "a law function (name law_...) that does not return "
                       "bool");
    return;
  }  /* if */
  a_scope_ptr scope = scope_for_routine(rout);
  s_add(laws, "/-- C++: %s -/\ndef %s : Prop :=\n  ",
        rout->source_corresp.name,
        safe_name(rout->source_corresp.name + sizeof(LAW_PREFIX) - 1));
  Str args = {NULL, 0, 0};
  a_variable_ptr params = scope->variant.routine.parameters;
  if (params != NULL) {
    s_add(laws, "forall");
    for (a_variable_ptr p = params; p != NULL; p = p->next) {
      const char *t = lean_type(p->type, pos);
      s_add(laws, " (%s : %s%s)", var_name(p),
            strcmp(t, "Bool") == 0 ? "" : "C.", t);
      s_add(&args, " %s", var_name(p));
    }  /* for */
    s_add(laws, ",\n    ");
  }  /* if */
  s_add(laws, "C.%s%s = true\n\n", name, s_get(&args));
}

/* The last part of a path: "dir/x.lean" -> "x.lean". */
static const char *base_name(const char *path)
{
  const char *b = path;
  for (const char *p = path; *p != '\0'; p++) {
    if (*p == '/' || *p == '\\') b = p + 1;
  }  /* for */
  return b;
}

/* The Lean module name of a file: "dir/Adder.lean" -> "Adder". */
static const char *module_name(const char *path)
{
  char *m = fmt("%s", base_name(path));
  char *dot = strrchr(m, '.');
  if (dot != NULL) *dot = '\0';
  return m;
}

static void write_file(const char *name, const Str *text)
{
  FILE *f = stdout;
  if (name != NULL && name[0] != '\0') {
    f = fopen(name, "w");
    if (f == NULL) {
      fprintf(stderr, "lean back end: cannot open %s\n", name);
      free_all_bufs();
      free_done_routines();
      exit(1);
    }  /* if */
  }  /* if */
  fputs(s_get(text), f);
  if (f != stdout) fclose(f);
}

static a_boolean is_user_struct(a_type_ptr type)
{
  return (type->kind == tk_struct || type->kind == tk_class) &&
         type->source_corresp.name != NULL &&
         type->variant.class_struct_union.field_list != NULL;
}

}  /* namespace lean_gen */

using namespace lean_gen;

void back_end(void)
/*
Entry point called by the front end (BACK_END_SHOULD_BE_CALLED) after the
translation unit has been processed.  The IL is not lowered.
*/
{
  Str out = {NULL, 0, 0};
  Str laws = {NULL, 0, 0};
  int n_laws = 0;
  a_scope_ptr file_scope = il_header.primary_scope;
  const char *src = il_header.primary_source_file != NULL ?
                      il_header.primary_source_file->file_name : "?";

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
    mark_done(r);
    if (is_law(r)) {
      gen_law(&laws, r);
      n_laws++;
    }  /* if */
  }  /* for */

  {
    Str all = {NULL, 0, 0};
    s_add(&all, "-- Generated by EDG cpfe-lean from %s.\n", src);
    s_add(&all, "-- Do not edit: run the translation again.\n\n");
    s_add(&all, "namespace C\n\n/-- C++ unsigned int -/\n"
                "abbrev U32 := BitVec 32\n\n");
    s_add(&all, "%s%send C\n", uses_mem ? MEM_PRELUDE : "", s_get(&out));
    out = all;
  }
  const char *out_name = getenv("EDG_LEAN_OUT");
  const char *laws_name = getenv("EDG_LEAN_LAWS_OUT");
  write_file(out_name, &out);
  if (laws_name != NULL && laws_name[0] != '\0') {
    if (out_name == NULL || out_name[0] == '\0') {
      fprintf(stderr, "lean back end: EDG_LEAN_LAWS_OUT needs EDG_LEAN_OUT "
                      "(the laws file imports the code module)\n");
      n_errors++;
    } else {
      Str lf = {NULL, 0, 0};
      s_add(&lf, "-- Generated by EDG cpfe-lean from the law_ functions in "
                 "%s.\n", src);
      s_add(&lf, "-- Do not edit: write the laws in C++ and run the "
                 "translation again.\n");
      s_add(&lf, "-- Each law: for all inputs, the C++ law function returns "
                 "true.\n\n");
      s_add(&lf, "import %s\n\nnamespace Laws\n\n%send Laws\n",
            module_name(out_name), s_get(&laws));
      if (n_laws == 0) {
        fprintf(stderr, "lean back end: no law_ functions found\n");
        n_errors++;
      }  /* if */
      write_file(laws_name, &lf);
    }  /* if */
  }  /* if */
  free_all_bufs();
  free_done_routines();
  cur_function = "";
  if (n_errors != 0) {
    fprintf(stderr, "lean back end: %d construct(s) not supported; the Lean "
                    "output is not complete.\n", n_errors);
    exit(1);
  }  /* if */
}
