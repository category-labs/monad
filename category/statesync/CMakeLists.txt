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

project(monad_statesync)

add_library(
  monad_statesync
  OBJECT
  # server
  "statesync_client.cpp"
  "statesync_client.h"
  "statesync_client_context.cpp"
  "statesync_client_context.hpp"
  "statesync_messages.h"
  "statesync_protocol.hpp"
  "statesync_protocol.cpp"
  "statesync_server.cpp"
  "statesync_server.h"
  "statesync_server_context.cpp"
  "statesync_server_context.hpp"
  "statesync_server_context.hpp"
  "statesync_version.cpp"
  "statesync_version.h")

target_include_directories(monad_statesync PUBLIC ${CATEGORY_MAIN_DIR})

monad_compile_options(monad_statesync)
target_link_libraries(monad_statesync PUBLIC monad_execution_ethereum)

monad_add_test_folder(".")

if(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
  add_executable(fuzz_statesync "${PROJECT_SOURCE_DIR}/test/fuzz_statesync.cpp")
  if(LIBFUZZER_RUNTIME_PATH AND EXISTS "${LIBFUZZER_RUNTIME_PATH}")
    target_compile_options(fuzz_statesync PRIVATE "-fsanitize=fuzzer-no-link")
  else()
    message(
      STATUS
        "Using default libFuzzer runtime for target fuzz_statesync; set LIBFUZZER_RUNTIME_PATH to use a libc++ build"
    )
    target_compile_options(fuzz_statesync PRIVATE "-fsanitize=fuzzer")
    target_link_options(fuzz_statesync PRIVATE "-fsanitize=fuzzer")
  endif()
  monad_compile_options(fuzz_statesync)
  target_link_libraries(fuzz_statesync PUBLIC monad_execution)
  if(LIBFUZZER_RUNTIME_PATH AND EXISTS "${LIBFUZZER_RUNTIME_PATH}")
    target_link_libraries(fuzz_statesync PRIVATE "${LIBFUZZER_RUNTIME_PATH}")
  endif()
endif()
