# Copyright (C) 2025 Category Labs, Inc.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

cmake_minimum_required(VERSION 3.27)

cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

project(monad)

set(CATEGORY_MAIN_DIR ${PROJECT_SOURCE_DIR})

if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
  if(CMAKE_CXX_COMPILER_VERSION VERSION_LESS 15)
    message(FATAL_ERROR "GCC version 15 or higher is required.")
  endif()
elseif(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
  if(CMAKE_CXX_COMPILER_VERSION VERSION_LESS 19)
    message(FATAL_ERROR "Clang version 19 or higher is required.")
  endif()
endif()

if(BUILD_SHARED_LIBS)
  # BUILD_SHARED_LIBS=ON does not automatically set -fPIC, leading to
  # relocations being emitted in object files that can't be patched
  set(CMAKE_POSITION_INDEPENDENT_CODE ON)
endif()

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

option(MONAD_COMPILER_LLVM "Build llvm backend" OFF)
option(MONAD_COMPILER_COVERAGE "Build with coverage" OFF)
option(MONAD_COMPILER_TESTING "Build compiler tests" OFF)
option(MONAD_COMPILER_BENCHMARKS "Build compiler benchmarks" OFF)
option(MONAD_COMPILER_DUMP_ASM "Dump assembly files into build/asm" OFF)
option(MONAD_COMPILER_STATS "Print statistics about the compiler" OFF)
option(MONAD_COMPILER_HOT_PATH_STATS "Print statistics about the vm" OFF)

if(NOT DEFINED BUILD_SHARED_LIBS)
  # If this isn't defined, evmone has the audacity to define it itself (to ON)
  # whereas the ordinary default is for static libraries; if it's not specified,
  # we explicitly set it to OFF, agreeing with the expected default and
  # preventing evmone from doing something different
  option(BUILD_SHARED_LIBS "Build monad with shared libraries" OFF)
endif()

include(cmake/test.cmake)

# ##############################################################################
# deps
# ##############################################################################

set(THIRD_PARTY_DIR "${PROJECT_SOURCE_DIR}/third_party")

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

  if(MONAD_COMPILER_TESTING)
    target_compile_definitions(${target} PUBLIC "MONAD_COMPILER_TESTING=1")
  endif()

  if(MONAD_COMPILER_STATS)
      target_compile_definitions(${target} PUBLIC "MONAD_COMPILER_STATS=1")
  endif()

  if(MONAD_COMPILER_HOT_PATH_STATS)
      target_compile_definitions(${target} PUBLIC "MONAD_COMPILER_HOT_PATH_STATS=1")
  endif()

  target_compile_options(
    ${target}
    PUBLIC $<$<CXX_COMPILER_ID:GNU>:-Wno-attributes=clang::no_sanitize>)

  # this is needed to turn off ranges support in nlohmann_json, because the
  # ranges standard header triggers a clang bug which is fixed in trunk but not
  # currently available to us
  # https://gcc.gnu.org/bugzilla//show_bug.cgi?id=109647
  target_compile_definitions(${target} PUBLIC "JSON_HAS_RANGES=0")
endfunction()

find_package(Boost REQUIRED COMPONENTS fiber json CONFIG)
find_package(PkgConfig REQUIRED)
pkg_check_modules(brotli REQUIRED IMPORTED_TARGET libbrotlienc libbrotlidec)
pkg_check_modules(crypto++ IMPORTED_TARGET libcrypto++)
pkg_check_modules(zstd REQUIRED IMPORTED_TARGET libzstd)

# In some Linux distributions, the pkgconfig file is called libcryptopp.pc
# instead of libcrypto++.pc
if(NOT crypto++_FOUND)
  pkg_check_modules(cryptopp IMPORTED_TARGET libcryptopp)
  if(NOT cryptopp_FOUND)
    message(FATAL_ERROR "libcrypto++ not found (as libcrypto++ or libcryptopp)")
  endif()
  add_library(PkgConfig::crypto++ ALIAS PkgConfig::cryptopp)
endif()

# ankerl
add_library(ankerl_hash INTERFACE)
target_include_directories(ankerl_hash INTERFACE "third_party/ankerl")

# asmjit
set(ASMJIT_STATIC ON)
add_subdirectory(third_party/asmjit)

# BLAKE3
add_subdirectory(third_party/BLAKE3/c)

# blst
set(DOWNLOAD_BLST OFF)
include(cmake/blst.cmake)

# c-kzg-4844
add_subdirectory("third_party/c-kzg-4844-builder")

# cli11
find_package(CLI11 REQUIRED)

# concurrentqueue
add_subdirectory("third_party/concurrentqueue")

# cthash
add_subdirectory("third_party/cthash")

# ethash
set(ETHASH_TESTING NO)
add_subdirectory("third_party/ethash")

# immer
option(immer_BUILD_TESTS OFF)
option(immer_BUILD_EXAMPLES OFF)
option(immer_BUILD_EXTRAS OFF)
add_subdirectory("third_party/immer" SYSTEM)

# intx
add_subdirectory("third_party/intx")

# evmc
set(HUNTER_ENABLED OFF)
add_subdirectory("third_party/evmc")

# evmone
if (MONAD_COMPILER_TESTING OR MONAD_COMPILER_BENCHMARKS)
  include(cmake/evmone.cmake)
endif()

# komihash
add_library(komihash INTERFACE)
target_include_directories(komihash INTERFACE "third_party/komihash")

# LLVM
# Because LLVM is a large dependency, we only try to find it if it's
# explicitly enabled as part of the VM build: regular client builds don't need
# to use it.
if(UTILS_CLANG_TIDY_AUTO_CONST OR MONAD_COMPILER_LLVM)
  include(cmake/LinkLLVM.cmake)
  find_package(LLVM 19.1.7 REQUIRED CONFIG)
endif()

if(MONAD_COMPILER_LLVM)
  add_definitions(-DMONAD_COMPILER_LLVM)
endif()

# magic_enum
find_package(magic_enum REQUIRED)

# nanobench
add_subdirectory("third_party/nanobench")

# nlohmann_json
add_subdirectory("third_party/nlohmann_json" SYSTEM)

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
set(OLD_CMAKE_POLICY_VERSION_MINIMUM "${CMAKE_POLICY_VERSION_MINIMUM}")
set(CMAKE_POLICY_VERSION_MINIMUM "3.5")
add_subdirectory(third_party/silkpre)
set(CMAKE_POLICY_VERSION_MINIMUM "${OLD_CMAKE_POLICY_VERSION_MINIMUM}")
# undo the injection of ccache silkpre/ff does
set_property(GLOBAL PROPERTY RULE_LAUNCH_COMPILE)
set_property(GLOBAL PROPERTY RULE_LAUNCH_LINK)

# tbb
find_package(TBB REQUIRED)

# unordered_dense
add_subdirectory("third_party/unordered_dense")

# ##############################################################################
# unit tests
# ##############################################################################

set(TEST_DATA_DIR "${PROJECT_SOURCE_DIR}/test")
set(VM_DATA_DIR "${PROJECT_SOURCE_DIR}/test/vm/data")
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
  target_link_libraries(${target} monad_execution GTest::GTest GTest::Main)
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
  file(GLOB_RECURSE test_files CONFIGURE_DEPENDS ${target}/test_*.cpp
       ${target}/*_test.cpp)
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

add_subdirectory("category/async")
add_subdirectory("category/core")
add_subdirectory("category/mpt")
add_subdirectory("category/event")
add_subdirectory("category/execution")
add_subdirectory("category/rpc")
add_subdirectory("category/statesync")
add_subdirectory("category/vm")

# Assemble all the object libraries into complete monad runtime library,
# monad_execution
add_library(monad_execution)
target_link_libraries(
  monad_execution
  PUBLIC monad_core
         monad_async
         monad_trie
         monad_execution_ethereum
         monad_execution_native
         monad_rpc
         monad_statesync
         monad-vm
         monad-vm-core
         monad-vm-compiler
         monad-vm-evm
         monad-vm-interpreter
         monad-vm-runtime
         monad-vm-utils)

# ##############################################################################
# cmds
# ##############################################################################

add_subdirectory(${PROJECT_SOURCE_DIR}/cmd)

# ##############################################################################
# unit tests
# ##############################################################################

add_subdirectory(${PROJECT_SOURCE_DIR}/test/ethereum_test)
add_subdirectory(${PROJECT_SOURCE_DIR}/test/unit/common)
add_subdirectory(${PROJECT_SOURCE_DIR}/test/vm)

# ##############################################################################
# utilities
# ##############################################################################

if(UTILS_CLANG_TIDY_AUTO_CONST)
  add_subdirectory(${PROJECT_SOURCE_DIR}/utils)
endif()
