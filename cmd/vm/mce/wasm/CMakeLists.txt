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

cmake_minimum_required(VERSION 3.25)
project(mce-wasm LANGUAGES C CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(MONAD_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/../../../..")

if(EMSCRIPTEN)
    # Keep the native x86-64 runtime layout while lowering to browser wasm32.
    add_compile_options(-sMEMORY64=2 -fexceptions)
    add_link_options(-sMEMORY64=2 -fexceptions)
endif()

set(ASMJIT_STATIC ON CACHE BOOL "" FORCE)
set(ASMJIT_NO_JIT ON CACHE BOOL "" FORCE)
set(ASMJIT_NO_AARCH64 ON CACHE BOOL "" FORCE)
add_subdirectory("${MONAD_ROOT}/third_party/asmjit" asmjit)
add_subdirectory("${MONAD_ROOT}/third_party/unordered_dense" unordered_dense)

# Reuse only the portable primitives; do not inherit zkVM runtime/OS shims.
foreach(header
    category/core/runtime/uint256/intrinsics.hpp
    category/core/runtime/non_temporal_memory.hpp)
    configure_file("${MONAD_ROOT}/zkvm/${header}"
        "${CMAKE_CURRENT_BINARY_DIR}/portable/${header}" COPYONLY)
endforeach()

add_executable(mce-wasm
    bindings.cpp
    support.cpp
    "${MONAD_ROOT}/category/vm/compiler/ir/basic_blocks.cpp"
    "${MONAD_ROOT}/category/vm/compiler/ir/x86.cpp"
    "${MONAD_ROOT}/category/vm/compiler/ir/x86/emitter.cpp"
    "${MONAD_ROOT}/category/vm/compiler/ir/x86/virtual_stack.cpp")
target_include_directories(mce-wasm PRIVATE
    "${CMAKE_CURRENT_SOURCE_DIR}/include"
    "${CMAKE_CURRENT_BINARY_DIR}/portable"
    "${MONAD_ROOT}"
    "${MONAD_ROOT}/third_party/evmc/include"
    "${MONAD_ROOT}/third_party/ethash/include")
target_compile_definitions(mce-wasm PRIVATE MONAD_VM_COMPILER_OFFLINE)
target_link_libraries(mce-wasm PRIVATE asmjit::asmjit unordered_dense)

if(EMSCRIPTEN)
    set_target_properties(mce-wasm PROPERTIES SUFFIX ".mjs")
    target_link_options(mce-wasm PRIVATE
        --bind
        -sMODULARIZE=1
        -sEXPORT_NAME=createMce
        -sENVIRONMENT=web,worker,node
        -sALLOW_MEMORY_GROWTH=1
        -sSTACK_SIZE=2097152
        -sDISABLE_EXCEPTION_CATCHING=0
        -sFILESYSTEM=0)
endif()

include(CTest)
if(BUILD_TESTING AND EMSCRIPTEN)
    find_program(NODE_EXECUTABLE NAMES node REQUIRED)
    add_test(NAME mce-wasm
        COMMAND "${NODE_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/test.mjs"
            "$<TARGET_FILE:mce-wasm>")
endif()
