cmake_minimum_required(VERSION 3.20)

project(monad-compiler)

option(HUNTER_ENABLED OFF)

include(CTest)

option(MONAD_COMPILER_LLVM "Build llvm backend" OFF)

if(MONAD_COMPILER_LLVM)
    include(cmake/LinkLLVM.cmake)
    find_package(LLVM 19.1.7 REQUIRED CONFIG)
    add_definitions(-DMONAD_COMPILER_LLVM)
endif()

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

option(MONAD_COMPILER_STANDALONE "Build as a standalone project" ON)
option(MONAD_COMPILER_COVERAGE "Build with coverage" OFF)
option(MONAD_COMPILER_TESTING "Build compiler tests" ON)
option(MONAD_COMPILER_BENCHMARKS "Build compiler benchmarks" OFF)
option(MONAD_COMPILER_DUMP_ASM "Dump assembly files into build/asm" OFF)

include(cmake/MonadCompileOptions.cmake)

find_package(CLI11 REQUIRED)
find_package(TBB REQUIRED)

if(MONAD_COMPILER_TESTING)
    find_package(GTest REQUIRED)
endif()

if(MONAD_COMPILER_BENCHMARKS)
    find_package(benchmark REQUIRED)
endif()

set(ROOT_DIRECTORY "${PROJECT_SOURCE_DIR}")
configure_file(cmake/test_resource_data.h.in test/test_resource_data.h @ONLY)
set(TOP_CURRENT_BINARY_DIR "${CMAKE_CURRENT_BINARY_DIR}")

if(MONAD_COMPILER_STANDALONE)
    set(ETHASH_TESTING NO)
    add_subdirectory(third_party/ethash)

    add_subdirectory(third_party/intx)
    add_subdirectory(third_party/nlohmann_json)
endif()

if(MONAD_COMPILER_TESTING)
    add_definitions(-DMONAD_COMPILER_TESTING)
endif()

# evmone
set(BUILD_SHARED_LIBS OFF)

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

set(ethash_DIR "${CMAKE_CURRENT_LIST_DIR}/cmake/dummy")
set(intx_DIR "${CMAKE_CURRENT_LIST_DIR}/cmake/dummy")
set(nlohmann_json_DIR "${CMAKE_CURRENT_LIST_DIR}/cmake/dummy")

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

# asmjit
set(ASMJIT_STATIC ON)
add_subdirectory(third_party/asmjit)

add_subdirectory(libs/compiler)
add_subdirectory(libs/core)
add_subdirectory(libs/evm)
add_subdirectory(libs/fuzzing)
add_subdirectory(libs/interpreter)
if(MONAD_COMPILER_LLVM)
    add_subdirectory(libs/llvm)
endif()
add_subdirectory(libs/runtime)
add_subdirectory(libs/utils)
add_subdirectory(libs/vm)
add_subdirectory(cmd/parser)

if(MONAD_COMPILER_BENCHMARKS)
    add_subdirectory(cmd/mce)
    add_subdirectory(cmd/kernel-generator)
endif()

if(MONAD_COMPILER_TESTING OR MONAD_COMPILER_BENCHMARKS)
    add_subdirectory(test)
endif()
