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

# This cmake project can be used to build the client part of the monad event
# library without building all of libmonad_core.a or using the rest of the CMake
# build system, i.e., this can be used a top-level source directory to just
# build these components. This is useful for external third-party clients, and
# for the Rust build system.

project(monad_event)

option(MONAD_EVENT_DISABLE_LIBHUGETLBFS
  "Disable the `monad_event_open_ring_dir_fd` API function (removes dependency on libhugetlbfs" OFF)

add_library(
  monad_event
  "../core/cleanup.c"
  "../core/cleanup.h"
  "../core/format_err.c"
  "../core/format_err.h"
  "../core/likely.h"
  "../core/srcloc.h"
  "../core/event/event_iterator.h"
  "../core/event/event_iterator_inline.h"
  "../core/event/event_metadata.h"
  "../core/event/event_ring.c"
  "../core/event/event_ring.h"
  "../core/event/event_ring_util.c"
  "../core/event/event_ring_util.h"
  "../execution/ethereum/core/base_ctypes.h"
  "../execution/ethereum/core/eth_ctypes.h"
  "../execution/ethereum/event/exec_event_ctypes.h"
  "../execution/ethereum/event/exec_event_ctypes_metadata.c"
  "../execution/ethereum/event/exec_iter_help.h")

target_include_directories(monad_event PUBLIC "../..")
target_compile_definitions(monad_event PUBLIC _GNU_SOURCE)
target_compile_features(monad_event PUBLIC c_std_23)
target_compile_options(monad_event PRIVATE -Wall -Wextra -Wconversion -Werror)

if(MONAD_EVENT_DISABLE_LIBHUGETLBFS)
  target_compile_definitions(monad_event PRIVATE MONAD_EVENT_DISABLE_LIBHUGETLBFS)
else()
  find_library(libhugetlbfs NAMES hugetlbfs REQUIRED)
  target_sources(monad_event PRIVATE
    "../core/mem/hugetlb_path.c"
    "../core/mem/hugetlb_path.h")
  target_link_libraries(monad_event PRIVATE hugetlbfs)
endif()

option(MONAD_EVENT_BUILD_EXAMPLE
    "Build the example program that shows how to use the API" ON)

if (MONAD_EVENT_BUILD_EXAMPLE)
    add_executable(eventwatch "example/eventwatch.c")
    target_link_libraries(eventwatch PRIVATE monad_event)
endif()
