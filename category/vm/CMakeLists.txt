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

# Subcomponents

add_subdirectory(compiler)
add_subdirectory(core)
add_subdirectory(evm)
add_subdirectory(fuzzing)
add_subdirectory(interpreter)
add_subdirectory(runtime)
add_subdirectory(utils)

if(MONAD_COMPILER_LLVM)
    add_subdirectory(llvm)
endif()

# Main VM library (execution's entry point)

add_library(monad-vm OBJECT)

target_sources(monad-vm PRIVATE
    "code.hpp"
    "compiler.cpp"
    "compiler.hpp"
    "varcode_cache.cpp"
    "varcode_cache.hpp"
    "vm.cpp"
    "vm.hpp"
)

monad_compile_options(monad-vm)

target_include_directories(monad-vm
    PUBLIC ${CATEGORY_MAIN_DIR}
    PUBLIC ${CATEGORY_MAIN_DIR}/third_party/unordered_dense/include
)

target_link_libraries(monad-vm
    PUBLIC TBB::tbb
    PUBLIC intx::intx
    PUBLIC evmc::evmc
    PUBLIC asmjit::asmjit
    PUBLIC quill::quill
    PUBLIC monad-vm::monad-vm-compiler
    PUBLIC monad-vm::monad-vm-interpreter
    PRIVATE monad-vm::monad-vm-core
    PRIVATE monad-vm::monad-vm-runtime
    PRIVATE monad-vm::monad-vm-utils
)

add_library(monad-vm::monad-vm ALIAS monad-vm)

