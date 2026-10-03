# cpfe-lean: EDG front end + Lean-generating back end (lean_gen_be.c).
set(ALL_C_FILES "${CORE_FRONT_END_SOURCE_FILES}"
                "${PROJECT_SOURCE_DIR}/lean_gen_be.c")
macro_configuration_to_compile_definitions("cpfe-lean")
set_source_files_properties(${ALL_C_FILES} PROPERTIES LANGUAGE CXX)
add_executable(cpfe-lean ${ALL_C_FILES} ${TXT_FILES})
add_dependencies(cpfe-lean error-info)
add_dependencies(cpfe-all cpfe-lean)
add_softfloat_to_target("cpfe-lean")
