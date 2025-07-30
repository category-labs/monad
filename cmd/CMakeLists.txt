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

include_directories(${CMAKE_CURRENT_SOURCE_DIR})

find_package(CLI11 REQUIRED)

add_executable(
  monad
  monad/main.cpp
  monad/event.cpp
  monad/event.hpp
  monad/file_io.hpp
  monad/file_io.cpp
  monad/runloop_ethereum.cpp
  monad/runloop_ethereum.hpp
  monad/runloop_monad.cpp
  monad/runloop_monad.hpp)

monad_compile_options(monad)

target_link_libraries(monad PRIVATE monad_execution CLI11::CLI11)

add_executable(monad_cli monad_cli.cpp)
monad_compile_options(monad_cli)
target_link_libraries(monad_cli PUBLIC monad_execution CLI11::CLI11)

if(DEFINED ENV{GIT_COMMIT_HASH})
  set(GIT_COMMIT_HASH $ENV{GIT_COMMIT_HASH})
else()
  execute_process(
    COMMAND git rev-parse HEAD
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    OUTPUT_VARIABLE GIT_COMMIT_HASH
    OUTPUT_STRIP_TRAILING_WHITESPACE)
endif()

target_compile_definitions(monad PRIVATE GIT_COMMIT_HASH="${GIT_COMMIT_HASH}")
target_compile_definitions(monad_cli
                           PRIVATE GIT_COMMIT_HASH="${GIT_COMMIT_HASH}")

add_executable(eventcap eventcap.cpp)
monad_compile_options(eventcap)
target_compile_options(eventcap PRIVATE -Wno-c99-designator)
target_link_libraries(eventcap PRIVATE monad_core CLI11::CLI11)
target_compile_options(eventcap PRIVATE -Wno-missing-field-initializers)

add_subdirectory(vm/parser)

if(MONAD_COMPILER_BENCHMARKS)
    add_subdirectory(vm/mce)
    add_subdirectory(vm/kernel-generator)
endif()
