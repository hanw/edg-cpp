# cpfe-bend: EDG front end + Bend-generating back end (bend_gen_be.c).
set(ALL_C_FILES "${CORE_FRONT_END_SOURCE_FILES}"
                "${PROJECT_SOURCE_DIR}/bend_gen_be.c")
macro_configuration_to_compile_definitions("cpfe-bend")
set_source_files_properties(${ALL_C_FILES} PROPERTIES LANGUAGE CXX)
add_executable(cpfe-bend ${ALL_C_FILES} ${TXT_FILES})
add_dependencies(cpfe-bend error-info)
add_dependencies(cpfe-all cpfe-bend)
add_softfloat_to_target("cpfe-bend")
