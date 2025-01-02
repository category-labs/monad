cmake_minimum_required(VERSION 3.27)

cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

project(monad)

option(HUNTER_ENABLED OFF)

option(EVMONE_TRACING
       "Enable instruction-level tracing for the evmone interpreter" OFF)
option(ENABLE_CALL_TRACING "Enable call tracer" ON)
option(CMAKE_EXPORT_COMPILE_COMMANDS ON)
option(BUILD_SHARED_LIBS OFF)

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

  # this is needed to turn off ranges support in nlohmann_json, because the
  # ranges standard header triggers a clang bug which is fixed in trunk but not
  # currently available to us
  # https://gcc.gnu.org/bugzilla//show_bug.cgi?id=109647
  target_compile_definitions(${target} PUBLIC "JSON_HAS_RANGES=0")

  if(EVMONE_TRACING)
    target_compile_definitions(${target} PUBLIC EVMONE_TRACING=1)
  endif()

  if(ENABLE_CALL_TRACING)
    target_compile_definitions(${target} PUBLIC "ENABLE_CALL_TRACING=1")
  endif()
endfunction()

find_package(Boost REQUIRED COMPONENTS fiber json)
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
  if("${target}" MATCHES "test_statesync")
    gtest_discover_tests(
      ${target} DISCOVERY_MODE PRE_TEST
      PROPERTIES RUN_SERIAL
                 TRUE
                 ENVIRONMENT
                 ASAN_OPTIONS=abort_on_error=1
                 ENVIRONMENT
                 UBSAN_OPTIONS=halt_on_error=1,print_stacktrace=1
                 ENVIRONMENT
                 TSAN_OPTIONS=external_symbolizer_path=/usr/bin/llvm-symbolizer)
  else()
    gtest_discover_tests(
      ${target} DISCOVERY_MODE PRE_TEST
      PROPERTIES ENVIRONMENT ASAN_OPTIONS=abort_on_error=1 ENVIRONMENT
                 UBSAN_OPTIONS=halt_on_error=1,print_stacktrace=1 ENVIRONMENT
                 TSAN_OPTIONS=external_symbolizer_path=/usr/bin/llvm-symbolizer)
  endif()
endfunction()

function(monad_add_test_folder target)
  file(GLOB_RECURSE test_files CONFIGURE_DEPENDS ${target}/test_*.cpp)
  foreach(test_file ${test_files})
    get_filename_component(test_name ${test_file} NAME_WLE)
    monad_add_test2(${test_name} ${test_file})
  endforeach()
endfunction()

function(monad_add_test_death target)
  cmake_parse_arguments(ADD_DEATH_TEST "" "FAIL_REGEX"
    "SOURCES;LINK_LIBRARIES;TEST_PROPERTIES" ${ARGN})
  if(NOT ADD_DEATH_TEST_FAIL_REGEX)
    message(FATAL_ERROR "FATAL: FAIL_REGEX is mandatory")
  endif()
  add_executable(${target} ${ADD_DEATH_TEST_SOURCES})
  monad_compile_options(${target})
  target_link_libraries(${target} PUBLIC GTest::gtest_main
                        ${ADD_DEATH_TEST_LINK_LIBRARIES})
  add_test(NAME "${PROJECT_NAME}/${target}"
           COMMAND ${CMAKE_COMMAND} -E env $<TARGET_FILE:${target}>)
  set_tests_properties("${PROJECT_NAME}/${target}" PROPERTIES
           PASS_REGULAR_EXPRESSION "${ADD_DEATH_TEST_FAIL_REGEX}"
           ${ADD_DEATH_TEST_TEST_PROPERTIES}
           ENVIRONMENT ASAN_OPTIONS=abort_on_error=1 ENVIRONMENT
           UBSAN_OPTIONS=halt_on_error=1,print_stacktrace=1 ENVIRONMENT
           TSAN_OPTIONS=external_symbolizer_path=/usr/bin/llvm-symbolizer)
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
