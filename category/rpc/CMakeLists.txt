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

project(monad_rpc)

add_library(
  monad_rpc
  OBJECT
  # rpc
  "eth_call.cpp" "eth_call.h")

target_include_directories(monad_rpc PUBLIC ${CATEGORY_MAIN_DIR})

monad_compile_options(monad_rpc)
target_link_libraries(monad_rpc PRIVATE monad_execution_native)

monad_add_test_folder(".")
