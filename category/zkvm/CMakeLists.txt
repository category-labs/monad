# Copyright (C) 2025-26 Category Labs, Inc.
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

# Standalone CMake project that builds the Monad VM components for zkVM
# targets. Produces libmonad-zkvm.a without requiring the full monad
# dependency tree (no TBB, Boost, asmjit, quill, etc.).
#
# Usage:
#   cmake -B build-zkvm -S category/zkvm \
#       -DCMAKE_TOOLCHAIN_FILE=../../category/core/toolchains/riscv64-elf-toolchain.cmake \
#       -DRISCV_TOOLCHAIN_DIR=/path/to/riscv
#   cmake --build build-zkvm

cmake_minimum_required(VERSION 3.20)
project(monad-zkvm LANGUAGES C CXX ASM)

set(MONAD_ZKVM ON)

# Testing features are incompatible with bare-metal zkVM builds.
if(MONAD_COMPILER_TESTING)
    message(FATAL_ERROR "MONAD_COMPILER_TESTING is not supported in zkVM builds")
endif()

# Backend selection — determines which allocator (and future vendor-specific
# syscall) implementations are linked.
set(MONAD_ZKVM_BACKEND "zisk" CACHE STRING "zkVM backend (zisk or sp1)")
set_property(CACHE MONAD_ZKVM_BACKEND PROPERTY STRINGS zisk sp1)

string(TOUPPER "${MONAD_ZKVM_BACKEND}" _ZKVM_BACKEND_UPPER)

# Point to the monad repository root
set(MONAD_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/../..")
set(CATEGORY_MAIN_DIR "${MONAD_ROOT}")
set(THIRD_PARTY_DIR "${MONAD_ROOT}/third_party")

# Reuse the shared compile options
include("${MONAD_ROOT}/cmake/compile_options.cmake")

# -------------------------------------------------------------------
# Third-party dependencies (minimal for bare-metal)
# -------------------------------------------------------------------

# intx (header-only uint256 implementation)
add_subdirectory("${THIRD_PARTY_DIR}/intx" intx)

# evmc — only need the header-only interface + instructions library.
# Skip loader (needs dlfcn.h), mocked_host, and tooling.
set(EVMC_INCLUDE_DIR "${THIRD_PARTY_DIR}/evmc/include")

add_library(evmc INTERFACE)
add_library(evmc::evmc ALIAS evmc)
target_compile_features(evmc INTERFACE c_std_99)
target_include_directories(evmc INTERFACE ${EVMC_INCLUDE_DIR})

add_library(evmc_cpp INTERFACE)
add_library(evmc::evmc_cpp ALIAS evmc_cpp)
target_compile_features(evmc_cpp INTERFACE cxx_std_17)
target_include_directories(evmc_cpp INTERFACE ${EVMC_INCLUDE_DIR})
target_link_libraries(evmc_cpp INTERFACE evmc::evmc)

add_subdirectory("${THIRD_PARTY_DIR}/evmc/lib/instructions" evmc_instructions)

# ethash — only keccak, no ethash or global_context (needs std::mutex)
set(ETHASH_BUILD_ETHASH OFF CACHE BOOL "" FORCE)
set(ETHASH_TESTING OFF CACHE BOOL "" FORCE)
set(ETHASH_INSTALL_CMAKE_CONFIG OFF CACHE BOOL "" FORCE)
add_subdirectory("${THIRD_PARTY_DIR}/ethash" ethash)

# -------------------------------------------------------------------
# VM component libraries
# -------------------------------------------------------------------

add_subdirectory("${MONAD_ROOT}/category/vm/core" core)
add_subdirectory("${MONAD_ROOT}/category/vm/evm" evm)
add_subdirectory("${MONAD_ROOT}/category/vm/runtime" runtime)
add_subdirectory("${MONAD_ROOT}/category/vm/interpreter" interpreter)

# The interpreter includes a few header-only utils (debug.hpp, traits.hpp,
# scope_exit.hpp) but we do not build the full utils library for zkVM.
# Provide the include path so the headers resolve.
target_include_directories(monad-vm-interpreter PUBLIC "${MONAD_ROOT}")

# Shadow upstream uint256.hpp with the intx-backed version for zkVM.
# The BEFORE keyword ensures this is searched before the upstream includes.
set(ZKVM_INCLUDE_DIR "${MONAD_ROOT}/category/zkvm/include")

foreach(tgt monad-vm-core monad-vm-evm monad-vm-runtime monad-vm-interpreter)
    target_include_directories(${tgt} BEFORE PUBLIC "${ZKVM_INCLUDE_DIR}")
    target_compile_definitions(${tgt} PUBLIC "MONAD_ZKVM_${_ZKVM_BACKEND_UPPER}")
endforeach()

# -------------------------------------------------------------------
# Helper: apply common zkVM compile options to a target
# -------------------------------------------------------------------

function(monad_zkvm_compile_options target)
    monad_compile_options(${target})
    target_include_directories(${target} BEFORE PUBLIC "${ZKVM_INCLUDE_DIR}")
    target_include_directories(${target} PUBLIC "${MONAD_ROOT}")
    target_compile_definitions(${target} PUBLIC "MONAD_ZKVM_${_ZKVM_BACKEND_UPPER}")
endfunction()

# -------------------------------------------------------------------
# Extract setjmp/longjmp from the compiler's newlib libc.a.
# libc.a exists at configure time (it ships with the compiler), so we
# can extract the objects here for inclusion in the final archive.
# -------------------------------------------------------------------

execute_process(
    COMMAND ${CMAKE_C_COMPILER} -print-file-name=libc.a
    OUTPUT_VARIABLE _libc_a
    OUTPUT_STRIP_TRAILING_WHITESPACE
)

set(_newlib_dir "${CMAKE_CURRENT_BINARY_DIR}/_libc_objs")
file(MAKE_DIRECTORY "${_newlib_dir}")

if(EXISTS "${_libc_a}")
    foreach(_obj libc_a-setjmp.o)
        execute_process(
            COMMAND ${CMAKE_AR} x "${_libc_a}" "${_obj}"
            WORKING_DIRECTORY "${_newlib_dir}"
        )
    endforeach()
    file(GLOB _libc_objs "${_newlib_dir}/*.o")
    if(NOT _libc_objs)
        message(FATAL_ERROR "Failed to extract setjmp/longjmp objects from ${_libc_a}")
    endif()
else()
    message(FATAL_ERROR "libc.a not found via compiler query; setjmp/longjmp will be missing")
endif()

# -------------------------------------------------------------------
# Assemble all objects into a single static library
# -------------------------------------------------------------------

add_library(monad-zkvm-libc OBJECT
    "${CMAKE_CURRENT_SOURCE_DIR}/src/libc.cpp"
)
monad_zkvm_compile_options(monad-zkvm-libc)

add_library(monad-zkvm-libstdcxx OBJECT
    "${CMAKE_CURRENT_SOURCE_DIR}/src/libstdcxx.cpp"
)
monad_zkvm_compile_options(monad-zkvm-libstdcxx)

add_library(monad-zkvm STATIC
    $<TARGET_OBJECTS:monad-vm-core>
    $<TARGET_OBJECTS:monad-vm-evm>
    $<TARGET_OBJECTS:monad-vm-runtime>
    $<TARGET_OBJECTS:monad-vm-interpreter>
    $<TARGET_OBJECTS:monad-zkvm-libc>
    $<TARGET_OBJECTS:monad-zkvm-libstdcxx>
    ${_libc_objs}
)
