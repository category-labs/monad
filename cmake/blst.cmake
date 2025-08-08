set(BLST_SOURCE_DIR "${PROJECT_SOURCE_DIR}/third_party/blst")

enable_language(ASM)

add_library(blst STATIC
    "${BLST_SOURCE_DIR}/build/assembly.S"
    "${BLST_SOURCE_DIR}/src/server.c")

target_include_directories(blst PUBLIC ${BLST_SOURCE_DIR}/bindings)

# The compilation options and defintions match what build.sh would do; if you
# upgrade libblst, ensure this is still the case
target_compile_options(blst PRIVATE -Wall -Wextra -Werror)
target_compile_definitions(blst PRIVATE __ADX__)
set_target_properties(blst PROPERTIES POSITION_INDEPENDENT_CODE ON)

add_library(blst::blst ALIAS blst)
