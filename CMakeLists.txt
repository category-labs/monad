cmake_minimum_required(VERSION 3.27)

cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

project(monad)

option(HUNTER_ENABLED OFF)

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

  if(ENABLE_CALL_TRACING)
    target_compile_definitions(${target} PUBLIC "ENABLE_CALL_TRACING=1")
  endif()
endfunction()

find_package(Boost REQUIRED COMPONENTS fiber json)
find_package(PkgConfig REQUIRED)
pkg_check_modules(brotli REQUIRED IMPORTED_TARGET libbrotlienc libbrotlidec)

# BLAKE3
add_subdirectory(third_party/BLAKE3/c)

# cli11
find_package(CLI11 REQUIRED)

# ethash
set(ETHASH_TESTING NO)
add_subdirectory("third_party/ethash")

# intx
add_subdirectory("third_party/intx")

# compiler
set(MONAD_COMPILER_STANDALONE OFF)
set(MONAD_COMPILER_TESTING OFF)
add_subdirectory("third_party/compiler")
# TODO
target_compile_options(evmone PRIVATE "-Wno-attributes")
target_compile_options(evmone_precompiles PRIVATE "-Wno-attributes")

# komihash
add_library(komihash INTERFACE)
target_include_directories(komihash INTERFACE "third_party/komihash")

# rpmalloc
if(CMAKE_C_COMPILER_ID STREQUAL "GNU")
  set(RPMALLOC_TOOLCHAIN
      "gcc"
      CACHE STRING "")
  set(RPMALLOC_C_FLAGS ${CMAKE_C_FLAGS})
elseif(CMAKE_C_COMPILER_ID STREQUAL "Clang")
  set(RPMALLOC_TOOLCHAIN
      "clang"
      CACHE STRING "")
  # TODO clang 19
  set(RPMALLOC_C_FLAGS
      "${CMAKE_C_FLAGS} -Wno-format -Wno-pre-c11-compat -Wno-unknown-warning-option"
  )
else()
  message(FATAL_ERROR "unsupported compiler")
endif()
include(ExternalProject)
ExternalProject_Add(
  rpmalloc-external
  GIT_REPOSITORY "https://github.com/mjansson/rpmalloc.git"
  GIT_TAG "e4393ff85585d91400bcbad2e7266c011075b673" # 1.4.5
  CONFIGURE_COMMAND
    env CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER}
    CFLAGS=${RPMALLOC_C_FLAGS} CXXFLAGS=${CMAKE_CXX_FLAGS}
    LDFLAGS=${CMAKE_EXE_LINKER_FLAGS} ./configure.py --toolchain
    ${RPMALLOC_TOOLCHAIN}
  BUILD_COMMAND ninja -v
  BUILD_IN_SOURCE ON
  BUILD_BYPRODUCTS
    "${CMAKE_CURRENT_BINARY_DIR}/rpmalloc-external-prefix/src/rpmalloc-external/lib/linux/release/x86-64/librpmallocwrap.a"
  INSTALL_COMMAND "")
add_library(rpmallocwrap STATIC IMPORTED)
set_property(
  TARGET rpmallocwrap
  PROPERTY
    IMPORTED_LOCATION
    "${CMAKE_CURRENT_BINARY_DIR}/rpmalloc-external-prefix/src/rpmalloc-external/lib/linux/release/x86-64/librpmallocwrap.a"
)
add_dependencies(rpmallocwrap rpmalloc-external)

# quill
add_subdirectory("third_party/quill")
# TODO
target_compile_options(
  quill
  PUBLIC
    $<$<AND:$<CXX_COMPILER_ID:GNU>,$<CONFIG:Release>>:-Wno-stringop-overflow>)
target_compile_options(
  quill PUBLIC $<$<CXX_COMPILER_ID:GNU>:-Wno-tautological-compare>)

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
  target_link_libraries(${target} monad_execution monad_statesync monad_rpc
                        GTest::GTest GTest::Main)
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
  add_test(NAME "${PROJECT_NAME}/${target}" COMMAND ${CMAKE_COMMAND} -E env
                                                    $<TARGET_FILE:${target}>)
  set_tests_properties(
    "${PROJECT_NAME}/${target}"
    PROPERTIES PASS_REGULAR_EXPRESSION
               "${ADD_DEATH_TEST_FAIL_REGEX}"
               ${ADD_DEATH_TEST_TEST_PROPERTIES}
               ENVIRONMENT
               ASAN_OPTIONS=abort_on_error=1
               ENVIRONMENT
               UBSAN_OPTIONS=halt_on_error=1,print_stacktrace=1
               ENVIRONMENT
               TSAN_OPTIONS=external_symbolizer_path=/usr/bin/llvm-symbolizer)
endfunction()

# ##############################################################################
# libs
# ##############################################################################

add_subdirectory("libs/async")
add_subdirectory("libs/core")
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
