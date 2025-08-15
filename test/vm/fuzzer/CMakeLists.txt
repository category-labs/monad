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

add_executable(monad-compiler-fuzzer)

target_sources(monad-compiler-fuzzer PRIVATE
  assertions.cpp
  assertions.hpp
  compiler_hook.hpp
  fuzzer.cpp)

target_link_libraries(monad-compiler-fuzzer
  PRIVATE evmone::state
  PRIVATE evmone
  PRIVATE blockchain-test-vm
  PRIVATE monad-vm::monad-vm-fuzzing
  PRIVATE monad_execution
  PRIVATE CLI11::CLI11
)
monad_compile_options(monad-compiler-fuzzer)

# TODO(BSC): fix this via evmone
target_include_directories(monad-compiler-fuzzer
  PRIVATE "${ROOT_DIRECTORY}/third_party/evmone/test/state"
)


add_executable(monad-typechecker-fuzzer)

target_sources(monad-typechecker-fuzzer PRIVATE
  typechecker_fuzzer.cpp)

target_link_libraries(monad-typechecker-fuzzer
  PRIVATE monad-vm::monad-vm-fuzzing
  PRIVATE monad_execution
  PRIVATE CLI11::CLI11
)
monad_compile_options(monad-typechecker-fuzzer)
