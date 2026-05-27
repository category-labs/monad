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
#   cmake -B build-zkvm -S zkvm/guest \
#       -DCMAKE_TOOLCHAIN_FILE=$PWD/category/core/toolchains/riscv64-elf.cmake \
#       -DRISCV_TOOLCHAIN_DIR=/path/to/riscv
#   cmake --build build-zkvm --target monad-zkvm

cmake_minimum_required(VERSION 3.20)
project(monad-zkvm LANGUAGES C CXX ASM)

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

# Shadow certain headers with zkVM-specific implementations via a mirror
# tree at zkvm/category/... — the BEFORE keyword ensures these are searched
# before the upstream `category/...` headers.
set(ZKVM_INCLUDE_DIR "${MONAD_ROOT}/zkvm")

# zkVM-specific CMake helpers (compile options, source / link-library
# manipulation, mirror-source substitution).
include("${MONAD_ROOT}/cmake/zkvm.cmake")

# -------------------------------------------------------------------
# Third-party dependencies (minimal for bare-metal)
# -------------------------------------------------------------------

# unordered_dense (header-only hash map used by category/core/bytes.hpp)
add_subdirectory("${THIRD_PARTY_DIR}/unordered_dense" unordered_dense)

# evmc — only need the header-only interface.
set(EVMC_INCLUDE_DIR "${THIRD_PARTY_DIR}/evmc/include")

add_library(evmc INTERFACE)
add_library(evmc::evmc ALIAS evmc)
target_compile_features(evmc INTERFACE c_std_99)
target_include_directories(evmc INTERFACE ${EVMC_INCLUDE_DIR})

# ethash — only keccak, no ethash or global_context (needs std::mutex)
set(ETHASH_BUILD_ETHASH OFF CACHE BOOL "" FORCE)
set(ETHASH_TESTING OFF CACHE BOOL "" FORCE)
set(ETHASH_INSTALL_CMAKE_CONFIG OFF CACHE BOOL "" FORCE)
add_subdirectory("${THIRD_PARTY_DIR}/ethash" ethash)

# -------------------------------------------------------------------
# VM component libraries
# -------------------------------------------------------------------

# Stub for monad-vm-utils — the interpreter unconditionally links it, but
# the utils library itself is not buildable in the zkVM environment (TBB,
# Boost, etc.). Header-only utils used by the interpreter (debug.hpp,
# traits.hpp, scope_exit.hpp) are reached via the MONAD_ROOT include path
# added below.
add_library(monad-vm-utils INTERFACE)
add_library(monad-vm::monad-vm-utils ALIAS monad-vm-utils)

add_subdirectory("${MONAD_ROOT}/category/vm/evm" evm)
add_subdirectory("${MONAD_ROOT}/category/vm/runtime" runtime)
add_subdirectory("${MONAD_ROOT}/category/vm/interpreter" interpreter)

# Strip x86-only assembly from the otherwise shared targets.
monad_zkvm_drop_sources(monad-vm-runtime
    "context\\.S" "exit\\.S" "math\\.S" "transmute\\.S")
monad_zkvm_drop_sources(monad-vm-interpreter "entry\\.S")

foreach(tgt monad-vm-evm monad-vm-runtime monad-vm-interpreter)
    monad_zkvm_compile_options(${tgt})
    target_link_libraries(${tgt} PUBLIC unordered_dense)
endforeach()

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
            RESULT_VARIABLE _ar_result
            ERROR_VARIABLE _ar_error
        )
        if(NOT _ar_result EQUAL 0)
            message(FATAL_ERROR
                "Failed to extract ${_obj} from ${_libc_a} "
                "(${CMAKE_AR} exited with ${_ar_result}): ${_ar_error}")
        endif()
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

add_library(monad-zkvm-core OBJECT
    "${ZKVM_INCLUDE_DIR}/core/libc.cpp"
    "${ZKVM_INCLUDE_DIR}/core/libstdcxx.cpp"
)
monad_compile_options(monad-zkvm-core)
monad_zkvm_compile_options(monad-zkvm-core)

add_library(monad-zkvm STATIC
    $<TARGET_OBJECTS:monad-zkvm-core>
    $<TARGET_OBJECTS:monad-vm-evm>
    $<TARGET_OBJECTS:monad-vm-runtime>
    $<TARGET_OBJECTS:monad-vm-interpreter>
    ${_libc_objs}
)
