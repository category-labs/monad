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

set(CMAKE_SYSTEM_NAME Generic)
set(CMAKE_SYSTEM_PROCESSOR riscv64)
set(CMAKE_TRY_COMPILE_TARGET_TYPE STATIC_LIBRARY)

# Configurable toolchain directory — pass -DRISCV_TOOLCHAIN_DIR=<path> to cmake.
set(RISCV_TOOLCHAIN_DIR "/opt/riscv" CACHE PATH "RISC-V toolchain directory")
list(APPEND CMAKE_TRY_COMPILE_PLATFORM_VARIABLES RISCV_TOOLCHAIN_DIR)

# Auto-detect target prefix (riscv64-none-elf- for nix, riscv64-unknown-elf- for ZisK).
if(EXISTS "${RISCV_TOOLCHAIN_DIR}/bin/riscv64-none-elf-gcc")
    set(RISCV_PREFIX "riscv64-none-elf-")
elseif(EXISTS "${RISCV_TOOLCHAIN_DIR}/bin/riscv64-unknown-elf-gcc")
    set(RISCV_PREFIX "riscv64-unknown-elf-")
else()
    message(FATAL_ERROR "No riscv64 gcc found in ${RISCV_TOOLCHAIN_DIR}/bin/")
endif()

set(CMAKE_C_COMPILER "${RISCV_TOOLCHAIN_DIR}/bin/${RISCV_PREFIX}gcc")
set(CMAKE_CXX_COMPILER "${RISCV_TOOLCHAIN_DIR}/bin/${RISCV_PREFIX}g++")
set(CMAKE_AR "${RISCV_TOOLCHAIN_DIR}/bin/${RISCV_PREFIX}ar")

set(CMAKE_C_FLAGS_INIT
    "-march=rv64ima -mabi=lp64 -mcmodel=medany -nostartfiles -nostdlib -ffunction-sections -fdata-sections")
set(CMAKE_CXX_FLAGS_INIT
    "-march=rv64ima -mabi=lp64 -mcmodel=medany -nostartfiles -nostdlib++ -fno-exceptions -fno-rtti -ffunction-sections -fdata-sections")
set(CMAKE_ASM_FLAGS_INIT "-march=rv64ima -mabi=lp64")

set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)
