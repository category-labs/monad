cmake_minimum_required(VERSION 3.27)

cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

project(monad)

option(HUNTER_ENABLED OFF)

option(EVMONE_TRACING
       "Enable instruction-level tracing for the evmone interpreter" OFF)
option(CMAKE_EXPORT_COMPILE_COMMANDS ON)
option(BUILD_SHARED_LIBS OFF)
option(MONAD_EMIT_CODE_COVERAGE OFF)

include(cmake/test.cmake)

# ##############################################################################
# deps
# ##############################################################################

function(monad_compile_options target)
  set_property(TARGET ${target} PROPERTY C_STANDARD 23)
  set_property(TARGET ${target} PROPERTY C_STANDARD_REQUIRED ON)
  set_property(TARGET ${target} PROPERTY CXX_STANDARD 23)
  set_property(TARGET ${target} PROPERTY CXX_STANDARD_REQUIRED ON)

  target_compile_options(${target} PRIVATE -Wall -Wextra -Wconversion -Werror)
  target_compile_definitions(${target} PUBLIC "_GNU_SOURCE")

  target_compile_options(
    ${target} PRIVATE $<$<CXX_COMPILER_ID:GNU>:-Wno-missing-field-initializers>)

  target_compile_definitions(${target} PUBLIC QUILL_ROOT_LOGGER_ONLY)

  target_compile_options(
    ${target}
    PUBLIC $<$<CXX_COMPILER_ID:GNU>:-Wno-attributes=clang::no_sanitize>)

  # needed to resolve some potential false positives when compiling with
  # Boost.Graph
  target_compile_options(
    ${target} PUBLIC $<$<CXX_COMPILER_ID:GNU>:-Wno-maybe-uninitialized>)

  # this is needed to turn off ranges support in nlohmann_json, because the
  # ranges standard header triggers a clang bug which is fixed in trunk but not
  # currently available to us
  # https://gcc.gnu.org/bugzilla//show_bug.cgi?id=109647
  target_compile_definitions(${target} PUBLIC "JSON_HAS_RANGES=0")

  if(EVMONE_TRACING)
    target_compile_definitions(${target} PUBLIC EVMONE_TRACING=1)
  endif()

  # monad code coverage report
  if(MONAD_EMIT_CODE_COVERAGE)
    target_compile_options(${target} PRIVATE --coverage)
    target_link_options(${target} PUBLIC --coverage)
  endif()
endfunction()

find_package(Boost REQUIRED COMPONENTS fiber graph json)
find_package(PkgConfig REQUIRED)
pkg_check_modules(brotli REQUIRED IMPORTED_TARGET libbrotlienc libbrotlidec)

# cli11
find_package(CLI11 REQUIRED)

# intx
add_subdirectory(third_party/intx)

# ethash
set(ETHASH_TESTING NO)
add_subdirectory("third_party/ethash")

# evmone
set(ethash_DIR "${CMAKE_CURRENT_LIST_DIR}/cmake/dummy")
set(intx_DIR "${CMAKE_CURRENT_LIST_DIR}/cmake/dummy")
add_subdirectory(third_party/evmone)
unset(ethash_DIR)
unset(intx_DIR)
target_link_libraries(evmone_precompiles PUBLIC ethash::keccak)
target_include_directories(evmone PUBLIC "third_party/evmone/lib")
# always compile baseline with optimization due to stack size of dispatch_cgoto
set_source_files_properties(
  third_party/evmone/lib/evmone/baseline.cpp TARGET_DIRECTORY evmone
  PROPERTIES COMPILE_OPTIONS -O2)

# komihash
add_library(komihash INTERFACE)
target_include_directories(komihash INTERFACE "third_party/komihash")

# silkpre
set(OPTIONAL_BUILD_TESTS OFF)
add_subdirectory(third_party/silkpre)
# undo the injection of ccache silkpre/ff does
set_property(GLOBAL PROPERTY RULE_LAUNCH_COMPILE)
set_property(GLOBAL PROPERTY RULE_LAUNCH_LINK)

# tbb
find_package(TBB REQUIRED)

# thread-safe-lru
add_library(thread_safe_lru INTERFACE)
target_include_directories(thread_safe_lru
                           INTERFACE "third_party/thread-safe-lru")

# ##############################################################################
# unit tests
# ##############################################################################

set(TEST_DATA_DIR "${PROJECT_SOURCE_DIR}/test")
set(THIRD_PARTY_DIR "${PROJECT_SOURCE_DIR}/third_party")
configure_file(cmake/test_resource_data.h.in test/test_resource_data.h @ONLY)

set(TOP_CURRENT_BINARY_DIR "${CMAKE_CURRENT_BINARY_DIR}")
function(monad_add_test2 target)
  add_executable(
    ${target}
    "${CMAKE_CURRENT_FUNCTION_LIST_DIR}/test/unit/common/src/test/main.cpp"
    ${ARGN})
  monad_compile_options(${target})
  target_compile_options(${target} PUBLIC "-Wno-missing-field-initializers"
  )# TODO
  target_include_directories(
    ${target}
    PRIVATE "${CMAKE_CURRENT_FUNCTION_LIST_DIR}/test/unit/common/include")
  target_include_directories(${target} PRIVATE "${TOP_CURRENT_BINARY_DIR}/test")
  target_link_libraries(${target} monad_execution monad_statesync GTest::GTest
                        GTest::Main)
  gtest_discover_tests(
    ${target} DISCOVERY_MODE PRE_TEST
    PROPERTIES ENVIRONMENT ASAN_OPTIONS=abort_on_error=1 ENVIRONMENT
               UBSAN_OPTIONS=halt_on_error=1,print_stacktrace=1 ENVIRONMENT
               TSAN_OPTIONS=external_symbolizer_path=/usr/bin/llvm-symbolizer)
endfunction()

function(monad_add_test_folder target)
  file(GLOB_RECURSE test_files CONFIGURE_DEPENDS ${target}/test_*.cpp)
  foreach(test_file ${test_files})
    get_filename_component(test_name ${test_file} NAME_WLE)
    monad_add_test2(${test_name} ${test_file})
  endforeach()
endfunction()

function(monad_target_gdb_pretty_printer dest target printer)
  file(REAL_PATH "${printer}" printer)
  file(RELATIVE_PATH leaf "${CMAKE_SOURCE_DIR}" "${printer}")
  set(asmfile "${CMAKE_BINARY_DIR}/${leaf}.S")
  set(GDB_PRETTY_PRINTER_PATH "${printer}")
  configure_file("${CMAKE_CURRENT_FUNCTION_LIST_DIR}/cmake/debug_gdb_scripts.in"
                 "${asmfile}" @ONLY)
  add_library(${target} OBJECT "${asmfile}")
  # The use of TARGET_OBJECTS here turns out to be critical. This was very
  # non-obvious.
  target_link_libraries(${dest} PUBLIC "$<TARGET_OBJECTS:${target}>")
endfunction()

function(monad_add_coverage_processing_tests)
  if(MONAD_EMIT_CODE_COVERAGE AND "${CMAKE_CURRENT_BINARY_DIR}" STREQUAL
                                  "${CMAKE_BINARY_DIR}")
    # .gcda files append per run, so they must be removed before every coverage
    # run
    add_test(
      NAME ${PROJECT_NAME}/PreCoverageSetup
      COMMAND find . -type f -name '*.gcda' -delete
      WORKING_DIRECTORY "${CMAKE_BUILD_DIR}")
    set_tests_properties(${PROJECT_NAME}/PreCoverageSetup
                         PROPERTIES FIXTURES_SETUP COVERAGE RUN_SERIAL ON)
    find_program(GCOVR_COMMAND gcovr REQUIRED DOC "path to the gcovr program")
    set(gcov_command)
    if(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
      string(REPLACE "clang++" "llvm-cov" llvmcov "${CMAKE_CXX_COMPILER}")
      find_program(LLVMCOV_COMMAND "${llvmcov}" REQUIRED
                   DOC "path to the llvm-cov program")
      set(gcov_command "${LLVMCOV_COMMAND} gcov")
    else()
      string(REPLACE "g++" "gcov" gcov "${CMAKE_CXX_COMPILER}")
      find_program(GCOV_COMMAND "${gcov}" REQUIRED
                   DOC "path to the gcov program")
      set(gcov_command "${GCOV_COMMAND}")
    endif()
    add_test(
      NAME ${PROJECT_NAME}/PostCoverageCleanup
      COMMAND
        ${GCOVR_COMMAND} --gcov-executable "${gcov_command}" -r
        "${CMAKE_SOURCE_DIR}" --exclude=.*/third_party/.*
        --gcov-ignore-parse-errors --exclude-throw-branches --branches -p
        --txt=coverage.txt --html-details=coverage_report.html
      WORKING_DIRECTORY "${CMAKE_BUILD_DIR}")
    set_tests_properties(${PROJECT_NAME}/PostCoverageCleanup
                         PROPERTIES FIXTURES_CLEANUP COVERAGE RUN_SERIAL ON)
    find_program(BASH_COMMAND bash REQUIRED DOC "path to the bash program")
    add_test(
      NAME ${PROJECT_NAME}/CoveragePrintSummary
      COMMAND
        "${BASH_COMMAND}" -c
        "echo \"\n\n          *** A much nicer HTML edition of this has been written to coverage_report.html ***\n\n\" >> coverage.txt && dd if=coverage.txt of=/dev/tty bs=65536"
      WORKING_DIRECTORY "${CMAKE_BUILD_DIR}")
    set_tests_properties(
      ${PROJECT_NAME}/CoveragePrintSummary
      PROPERTIES DEPENDS ${PROJECT_NAME}/PostCoverageCleanup RUN_SERIAL ON)
  endif()
endfunction()

# ##############################################################################
# libs
# ##############################################################################

add_subdirectory("libs/core")
add_subdirectory("libs/runloop")
add_subdirectory("libs/async")
add_subdirectory("libs/db")
add_subdirectory("libs/execution")
add_subdirectory("libs/rpc")
add_subdirectory("libs/statesync")

# ##############################################################################
# cmds
# ##############################################################################

add_subdirectory(${PROJECT_SOURCE_DIR}/cmd)

# ##############################################################################
# unit tests
# ##############################################################################

add_subdirectory(${PROJECT_SOURCE_DIR}/test/ethereum_test)
add_subdirectory(${PROJECT_SOURCE_DIR}/test/unit/common)

monad_add_coverage_processing_tests()
