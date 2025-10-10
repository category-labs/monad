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

# Testing VM

add_library(blockchain-test-vm STATIC)

if(MONAD_COMPILER_LLVM)
    monad_link_llvm(blockchain-test-vm)
    target_link_libraries(blockchain-test-vm
        PUBLIC monad-vm::monad-vm-llvm
    )
endif()

target_sources(blockchain-test-vm
    PRIVATE
        test_vm.hpp
        test_vm.cpp
)

target_link_libraries(blockchain-test-vm
    PUBLIC
        evmone
        evmc::evmc
        monad-vm::monad-vm
        monad-vm::monad-vm-compiler
        monad-vm::monad-vm-evm
        monad-vm::monad-vm-interpreter
        monad-vm::monad-vm-untyped-ir-interpreter
)

target_include_directories(blockchain-test-vm
    PUBLIC .
    PUBLIC "${CATEGORY_MAIN_DIR}/third_party/evmone/test/state"
)
monad_compile_options(blockchain-test-vm)
