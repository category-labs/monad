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

# This cmake project can be used to build just the execution event SDK library
# (as `libmonad_event.a`) without building all of the monolithic
# libmonad_execution.a or including the rest of the CMake build system. This
# is useful for external third-party clients, and for the Rust build system.

cmake_minimum_required(VERSION 3.23)

project(monad_event LANGUAGES C CXX)

if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  set(MONAD_EVENT_HUGETLBFS_DEFAULT ON)
  set(MONAD_EVENT_USE_O_TMPFILE_DEFAULT OFF) # OFF until Ubuntu 26.04 LTS
else()
  set(MONAD_EVENT_HUGETLBFS_DEFAULT OFF)
  set(MONAD_EVENT_USE_O_TMPFILE_DEFAULT OFF)
endif()

option(MONAD_EVENT_USE_LIBHUGETLBFS
  "Disable the default value in the `monad_event_open_hugetlbfs_dir_fd` API function (removes dependency on libhugetlbfs)"
  ${MONAD_EVENT_HUGETLBFS_DEFAULT})

option(MONAD_EVENT_USE_O_TMPFILE
  "Use the O_TMPFILE method of hiding in-progress file writes (requires Linux kernel 6.10+ for unprivileged users)"
  ${MONAD_EVENT_USE_O_TMPFILE_DEFAULT})

find_package(zstd REQUIRED)

# libgmp is not required, but if it is available, it can be used by the C++20
# std::formatter specialization of `monad_c_uint256_ne` to do basic integer
# to UTF-8 conversion via gmp_snprintf by default
find_library(libgmp_file gmp)

add_library(
  monad_event
  "../core/assert.c"
  "../core/cleanup.c"
  "../core/format_err.c"
  "../core/path_util.c"
  "../core/event/evcap_reader.c"
  "../core/event/evcap_writer.c"
  "../core/event/event_ring.c"
  "../core/event/event_ring_util.c"
  "../core/event/test_event_ctypes_metadata.c"
  "../core/mem/virtual_buf.c"
  "../execution/ethereum/event/blockcap_archive.c"
  "../execution/ethereum/event/blockcap_builder.c"
  "../execution/ethereum/event/blockcap_finalize_tracker.c"
  "../execution/ethereum/event/blockcap_pack_writer.c"
  "../execution/ethereum/event/blockcap_shared.c"
  "../execution/ethereum/event/exec_event_ctypes_metadata.c")

target_sources(monad_event PUBLIC
  FILE_SET event_headers
  TYPE HEADERS
  BASE_DIRS ".."
  FILES
  "../core/assert.h"
  "../core/cleanup.h"
  "../core/format_err.h"
  "../core/hex.hpp"
  "../core/likely.h"
  "../core/path_util.h"
  "../core/srcloc.h"
  "../core/event/evcap_file.h"
  "../core/event/evcap_reader.h"
  "../core/event/evcap_reader_inline.h"
  "../core/event/evcap_writer.h"
  "../core/event/evcap_writer_inline.h"
  "../core/event/event_def.h"
  "../core/event/event_metadata.h"
  "../core/event/event_recorder.h"
  "../core/event/event_recorder_inline.h"
  "../core/event/event_ring.h"
  "../core/event/event_ring_inline.h"
  "../core/event/event_ring_iter.h"
  "../core/event/event_ring_fmt.hpp"
  "../core/event/event_ring_util.h"
  "../core/event/test_event_ctypes.h"
  "../core/mem/align.h"
  "../core/mem/virtual_buf.h"
  "../core/mem/virtual_buf_inline.h"
  "../execution/ethereum/core/base_ctypes.h"
  "../execution/ethereum/core/eth_ctypes.h"
  "../execution/ethereum/core/fmt/base_ctypes_fmt.hpp"
  "../execution/ethereum/core/fmt/eth_ctypes_fmt.hpp"
  "../execution/ethereum/event/blockcap.h"
  "../execution/ethereum/event/exec_event_ctypes.h"
  "../execution/ethereum/event/exec_event_ctypes_fmt.hpp"
  "../execution/ethereum/event/exec_iter_help.h"
  "../execution/ethereum/event/exec_iter_help_inline.h"
  "../execution/monad/core/fmt/monad_ctypes_fmt.hpp"
  "../execution/monad/core/monad_ctypes.h")

target_include_directories(monad_event PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/../..>
    $<INSTALL_INTERFACE:include>)

if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  target_sources(monad_event PRIVATE "../core/event/event_ring_util_linux.c")
else()
  target_sources(monad_event PRIVATE "../core/event/event_ring_util_posix.c")
endif()

if(MONAD_EVENT_USE_O_TMPFILE)
  target_sources(monad_event PRIVATE "../execution/ethereum/event/blockcap_archive_linux.c")
  target_compile_definitions(monad_event PRIVATE MONAD_EVENT_USE_O_TMPFILE)
else()
  target_sources(monad_event PRIVATE "../execution/ethereum/event/blockcap_archive_posix.c")
endif()

if(APPLE)
  add_library(monad_event_os_compat
      "os-compat/memfd_create.c"
      "os-compat/posix_fallocate.c")
  target_sources(monad_event_os_compat PUBLIC
    FILE_SET event_headers_os_compat
    TYPE HEADERS
    BASE_DIRS "./os-compat"
    FILES
    "./os-compat/fcntl.h"
    "./os-compat/stdbit.h"
    "./os-compat/stdbit-builtin.h"
    "./os-compat/sys/mman.h")
  target_compile_features(monad_event_os_compat PUBLIC c_std_23)
  target_include_directories(monad_event_os_compat PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/os-compat>
    $<INSTALL_INTERFACE:include>)
  target_link_libraries(monad_event PUBLIC monad_event_os_compat)
endif()

target_compile_definitions(monad_event PUBLIC _GNU_SOURCE MONAD_EVENT_SDK_EXTERNAL)
target_compile_features(monad_event PUBLIC c_std_23)
target_compile_options(monad_event PRIVATE -Wall -Wextra -Wconversion -Werror)

if(MONAD_EVENT_USE_LIBHUGETLBFS)
  find_library(libhugetlbfs NAMES hugetlbfs REQUIRED)
  target_sources(monad_event PRIVATE
    "../core/mem/hugetlb_path.c"
    "../core/mem/hugetlb_path.h")
  target_link_libraries(monad_event PRIVATE hugetlbfs)
else()
  target_compile_definitions(monad_event PRIVATE MONAD_EVENT_DISABLE_LIBHUGETLBFS)
endif()

if(BUILD_SHARED_LIBS)
  target_link_libraries(monad_event PRIVATE zstd::libzstd_shared)
else()
  target_link_libraries(monad_event PRIVATE zstd::libzstd_static)
endif()

if(libgmp_file)
  target_compile_definitions(monad_event PUBLIC MONAD_EVENT_HAS_LIBGMP)
  target_link_libraries(monad_event PRIVATE ${libgmp_file})
else()
  message(WARNING "libgmp is not available; uint256 values > UINT128_MAX will print as hex uint64_t[4]")
endif()

option(MONAD_EVENT_BUILD_EXAMPLE
    "Build the example program that shows how to use the API" ON)

if (MONAD_EVENT_BUILD_EXAMPLE)
  add_executable(eventwatch "example/eventwatch.c")
  target_compile_options(eventwatch PRIVATE -Wall -Wextra -Wconversion -Werror)
  target_link_libraries(eventwatch PRIVATE monad_event)
endif()

if(APPLE)
  install(TARGETS monad_event monad_event_os_compat
          EXPORT monad_exec_events_sdk
          FILE_SET event_headers DESTINATION include/category
          FILE_SET event_headers_os_compat DESTINATION include)
else()
  install(TARGETS monad_event
          EXPORT monad_exec_events_sdk
          FILE_SET event_headers DESTINATION include/category)
endif()

install(EXPORT monad_exec_events_sdk
        FILE monad_exec_events_sdk.cmake
        DESTINATION lib/cmake/category-labs)

include(CMakePackageConfigHelpers)
configure_package_config_file(${CMAKE_CURRENT_SOURCE_DIR}/Config.cmake.in
  "${CMAKE_CURRENT_BINARY_DIR}/monad_exec_events_sdk-config.cmake"
  INSTALL_DESTINATION "lib/cmake/category-labs"
  NO_SET_AND_CHECK_MACRO
  NO_CHECK_REQUIRED_COMPONENTS_MACRO)

install(FILES
  "${CMAKE_CURRENT_BINARY_DIR}/monad_exec_events_sdk-config.cmake"
  DESTINATION lib/cmake/category-labs)

export(EXPORT monad_exec_events_sdk
  FILE "${CMAKE_CURRENT_BINARY_DIR}/monad_exec_events_sdk.cmake")
