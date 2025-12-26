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

add_library(monad-vm-test-utils OBJECT)

target_sources(monad-vm-test-utils PRIVATE
    "evm-as_utils.hpp"
    "test_context.hpp"
    "test_memory.hpp"
)

monad_compile_options(monad-vm-test-utils)

target_link_libraries(monad-vm-test-utils
    PUBLIC TBB::tbb
    PUBLIC intx::intx
    PUBLIC evmc::evmc
    PUBLIC asmjit::asmjit
    PUBLIC quill::quill
    PUBLIC monad-vm::monad-vm-compiler
    PUBLIC monad-vm::monad-vm-interpreter
    PUBLIC monad-vm::monad-vm-core
    PUBLIC monad-vm::monad-vm-runtime
    PUBLIC monad-vm::monad-vm-utils
)

add_library(monad-vm::monad-vm-test-utils ALIAS monad-vm-test-utils)
