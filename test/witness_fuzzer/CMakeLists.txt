# Copyright (C) 2026 Category Labs, Inc.
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

add_executable(monad-witness-fuzzer)

target_sources(monad-witness-fuzzer PRIVATE
  fuzzer.cpp)

target_link_libraries(monad-witness-fuzzer
  PRIVATE monad_execution
  PRIVATE monad-vm::monad-vm-fuzzing
  PRIVATE CLI11::CLI11
)
monad_compile_options(monad-witness-fuzzer)

target_include_directories(monad-witness-fuzzer
  PRIVATE "${TOP_CURRENT_BINARY_DIR}/test")
