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
    "ir/local_stacks.cpp"
    "ir/local_stacks.hpp"
    # polymorphic types
    "ir/poly_typed.hpp"
    "ir/poly_typed.cpp"
    "ir/poly_typed/block.hpp"
    "ir/poly_typed/exceptions.hpp"
    "ir/poly_typed/infer.cpp"
    "ir/poly_typed/infer.hpp"
    "ir/poly_typed/infer_state.cpp"
    "ir/poly_typed/infer_state.hpp"
    "ir/poly_typed/kind.cpp"
    "ir/poly_typed/kind.hpp"
    "ir/poly_typed/strongly_connected_components.cpp"
    "ir/poly_typed/strongly_connected_components.hpp"
    "ir/poly_typed/subst_map.cpp"
    "ir/poly_typed/subst_map.hpp"
    "ir/poly_typed/unify.cpp"
    "ir/poly_typed/unify.hpp"
    # untyped ir
    "ir/untyped.hpp"
    "ir/untyped.cpp"
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
    PUBLIC ${CATEGORY_MAIN_DIR}/third_party/unordered_dense/include
)

target_link_libraries(monad-vm-compiler
    PUBLIC intx::intx
    PUBLIC asmjit::asmjit
    PUBLIC evmc::evmc
    PUBLIC monad-vm::monad-vm-core
    PUBLIC monad-vm::monad-vm-evm
    PUBLIC monad-vm::monad-vm-runtime
    PUBLIC monad-vm::monad-vm-utils
    PUBLIC quill::quill
)

add_library(monad-vm::monad-vm-compiler ALIAS monad-vm-compiler)
