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
