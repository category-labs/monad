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

add_library(monad-vm-compiler OBJECT)

target_sources(monad-vm-compiler PRIVATE
    "transactional_unordered_map.hpp"
    "types.hpp"
    # IR
    "ir/basic_blocks.cpp"
    "ir/basic_blocks.hpp"
    "ir/instruction.hpp"
    # x86 backend
    "ir/x86.hpp"
    "ir/x86.cpp"
    "ir/x86/emitter.cpp"
    "ir/x86/emitter.hpp"
    "ir/x86/types.hpp"
    "ir/x86/virtual_stack.cpp"
    "ir/x86/virtual_stack.hpp"
)

monad_compile_options(monad-vm-compiler)

target_include_directories(monad-vm-compiler
    PUBLIC ${CATEGORY_MAIN_DIR}
)

target_link_libraries(monad-vm-compiler
    PUBLIC intx::intx
    PUBLIC asmjit::asmjit
    PUBLIC evmc::evmc
    PUBLIC monad-vm::monad-vm-evm
    PUBLIC monad-vm::monad-vm-runtime
    PUBLIC monad-vm::monad-vm-utils
    PUBLIC quill::quill
)

add_library(monad-vm::monad-vm-compiler ALIAS monad-vm-compiler)
