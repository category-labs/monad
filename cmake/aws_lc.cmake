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

include(ExternalProject)

function(monad_add_aws_lc)
  set(_source_dir "${PROJECT_SOURCE_DIR}/third_party/aws-lc")
  set(_bootstrap_dir "${CMAKE_BINARY_DIR}/aws-lc-bootstrap")
  set(_symbols "${CMAKE_BINARY_DIR}/aws-lc-prefix/symbols.txt")
  set(_archive "${_bootstrap_dir}/crypto/libcrypto.a")

  if(CMAKE_SYSTEM_NAME STREQUAL "Darwin")
    set(_object_file_format macho)
  elseif(CMAKE_SYSTEM_NAME STREQUAL "Windows")
    set(_object_file_format pe)
    if(MSVC)
      set(_archive "${_bootstrap_dir}/crypto/crypto.lib")
    endif()
  elseif(CMAKE_SYSTEM_NAME STREQUAL "Linux")
    set(_object_file_format elf)
  else()
    message(FATAL_ERROR
            "AWS-LC symbol prefixing does not support ${CMAKE_SYSTEM_NAME}")
  endif()

  find_program(_go NAMES go REQUIRED)

  set(_bootstrap_args
      "-DCMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE}"
      -DCMAKE_POSITION_INDEPENDENT_CODE=ON
      -DBUILD_SHARED_LIBS=OFF
      -DBUILD_TESTING=OFF
      -DBUILD_LIBSSL=OFF
      -DBUILD_TOOL=OFF
      -DDISABLE_GO=ON
      -DDISABLE_PERL=ON
      -DENABLE_SOURCE_MODIFICATION=OFF
      -DENABLE_SYMBOL_VERSIONING=OFF)

  foreach(_variable IN ITEMS
          CMAKE_TOOLCHAIN_FILE
          CMAKE_C_COMPILER
          CMAKE_C_COMPILER_TARGET
          CMAKE_C_FLAGS
          CMAKE_ASM_COMPILER
          CMAKE_ASM_FLAGS
          CMAKE_SYSROOT
          CMAKE_OSX_ARCHITECTURES)
    if(DEFINED ${_variable} AND NOT "${${_variable}}" STREQUAL "")
      list(APPEND _bootstrap_args "-D${_variable}=${${_variable}}")
    endif()
  endforeach()

  # AWS-LC's supported prefixing workflow requires an unprefixed archive first.
  ExternalProject_Add(
    monad_aws_lc_bootstrap
    SOURCE_DIR "${_source_dir}"
    BINARY_DIR "${_bootstrap_dir}"
    UPDATE_COMMAND ""
    CMAKE_ARGS ${_bootstrap_args}
    BUILD_COMMAND "${CMAKE_COMMAND}" --build <BINARY_DIR> --target crypto
    BUILD_BYPRODUCTS "${_archive}"
    BUILD_ALWAYS YES
    INSTALL_COMMAND "")

  add_custom_command(
    OUTPUT "${_symbols}"
    COMMAND "${CMAKE_COMMAND}" -E make_directory
            "${CMAKE_BINARY_DIR}/aws-lc-prefix"
    COMMAND "${_go}" run "${_source_dir}/util/read_symbols.go"
            -out "${_symbols}"
            -obj-file-format "${_object_file_format}"
            "${_archive}"
    WORKING_DIRECTORY "${_source_dir}"
    DEPENDS monad_aws_lc_bootstrap "${_archive}"
    VERBATIM)
  add_custom_target(monad_aws_lc_symbols DEPENDS "${_symbols}")

  block()
    set(CMAKE_POLICY_DEFAULT_CMP0077 NEW)
    set(BORINGSSL_PREFIX MONAD_AWS_LC)
    set(BORINGSSL_PREFIX_SYMBOLS "${_symbols}")
    set(GO_EXECUTABLE "${_go}")
    set(BUILD_SHARED_LIBS OFF)
    set(BUILD_TESTING OFF)
    set(BUILD_LIBSSL OFF)
    set(BUILD_TOOL OFF)
    set(DISABLE_GO OFF)
    set(DISABLE_PERL ON)
    set(ENABLE_SOURCE_MODIFICATION OFF)
    set(ENABLE_SYMBOL_VERSIONING OFF)
    set(CMAKE_POSITION_INDEPENDENT_CODE ON)
    add_subdirectory("${_source_dir}"
                     "${CMAKE_BINARY_DIR}/third_party/aws-lc"
                     EXCLUDE_FROM_ALL SYSTEM)
  endblock()

  add_dependencies(crypto monad_aws_lc_symbols)
  set_target_properties(crypto PROPERTIES OUTPUT_NAME aws_lc_crypto)
  add_library(aws_lc::crypto ALIAS crypto)

  if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
    target_link_options(crypto INTERFACE
                        "LINKER:--exclude-libs,libaws_lc_crypto.a")
  endif()
endfunction()
