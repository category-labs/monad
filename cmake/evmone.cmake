if (NOT IS_DIRECTORY "${PROJECT_SOURCE_DIR}/third_party/evmone")
    message(FATAL_ERROR "Building Category Labs internal VM differential      \
                         testing and benchmarking requires third_party/evmone \
                         to be present. Unset MONAD_COMPILER_TESTING and      \
                         MONAD_COMPILER_BENCHMARKS to build without           \
                         internal code.")
endif()

# evmone
set(HUNTER_ENABLED OFF)

# Both the test suite and the benchmark executables rely on the evmone state
# library, which is only built if `EVMONE_TESTING` is true. We don't want to
# build that code if we're in a client integration build.
if (MONAD_COMPILER_TESTING OR MONAD_COMPILER_BENCHMARKS)
    set(EVMONE_TESTING YES)
else()
    set(EVMONE_TESTING NO)
endif()

set(EVMONE_RUN_TESTS NO)
set(EVMC_TESTING NO)

set(ethash_DIR "${CMAKE_CURRENT_LIST_DIR}/dummy")
set(intx_DIR "${CMAKE_CURRENT_LIST_DIR}/dummy")
set(nlohmann_json_DIR "${CMAKE_CURRENT_LIST_DIR}/dummy")

add_subdirectory(third_party/evmone)

unset(ethash_DIR)
unset(intx_DIR)
unset(nlohmann_json_DIR)


target_link_libraries(evmone_precompiles PUBLIC ethash::keccak)
target_link_libraries(evmone PUBLIC ethash::keccak intx::intx)
target_include_directories(evmone PUBLIC "third_party/evmone/lib")

# always compile baseline with optimization due to stack size of dispatch_cgoto
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
# NOTE: GCC/G++ w. ASAN and -O2 enabled causes a mis-compilation in
# the baseline execution translation unit, when it calls
# `evmc_make_result`. The culprit is that ASAN writes a `\276` to
# memory on malloc. This value gets propagated to the result
# structure, which causes an assertion failure to trigger in our test
# fixture.
  set_source_files_properties(
    third_party/evmone/lib/evmone/baseline_execution.cpp
    TARGET_DIRECTORY evmone
    PROPERTIES
    COMPILE_OPTIONS "-O2;-fno-sanitize=all"
  )
else()
  set_source_files_properties(
    third_party/evmone/lib/evmone/baseline_execution.cpp
    TARGET_DIRECTORY evmone
    PROPERTIES
    COMPILE_OPTIONS -O2
  )
endif()

if(MONAD_COMPILER_TESTING OR MONAD_COMPILER_BENCHMARKS)
    target_link_libraries(evmone-state PUBLIC ethash::keccak intx::intx nlohmann_json::nlohmann_json)
    target_link_libraries(evmone-statetestutils PUBLIC nlohmann_json::nlohmann_json)
endif()

target_compile_options(evmone PRIVATE "-Wno-attributes")
target_compile_options(evmone_precompiles PRIVATE "-Wno-attributes")
