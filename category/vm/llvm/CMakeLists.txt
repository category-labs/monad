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

enable_language(ASM)

option(MONAD_VM_LLVM_DEBUG "Trace instructions executed by llvm backend" OFF)

# This option causes any binary that runs the Monad baseline interpreter to
# print a CSV-formatted summary of opcode executions when it exits. This code is
# not thread-safe and should only be enabled in appropriate benchmarking
# contexts, never in production.
option(MONAD_VM_LLVM_STATS "Print opcode statistics on program exit" OFF)

add_library(monad-vm-llvm OBJECT)

monad_link_llvm(monad-vm-llvm)

target_sources(monad-vm-llvm PRIVATE
  "entry.S"
  "execute.cpp"
  "execute.hpp"
  "emitter.hpp"
  "dependency_blocks.hpp"
  "llvm.cpp"
  "llvm.hpp"
  "llvm_state.hpp"
)

monad_compile_options(monad-vm-llvm)

if(MONAD_VM_LLVM_DEBUG)
  target_compile_definitions(monad-vm-llvm PRIVATE MONAD_VM_LLVM_DEBUG)
endif()

if(MONAD_VM_LLVM_STATS)
  target_compile_definitions(monad-vm-LLVM PRIVATE MONAD_VM_LLVM_STATS)
endif()

target_include_directories(monad-vm-llvm
    PUBLIC ${CATEGORY_MAIN_DIR}
)

target_link_libraries(monad-vm-llvm
    PUBLIC intx::intx
    PUBLIC evmc::evmc
    PUBLIC monad-vm::monad-vm-evm
    PUBLIC monad-vm::monad-vm-runtime
    PUBLIC monad-vm::monad-vm-utils
    PUBLIC monad-vm::monad-vm-compiler
    PRIVATE monad-vm::monad-vm-core
)

add_library(monad-vm::monad-vm-llvm ALIAS monad-vm-llvm)
