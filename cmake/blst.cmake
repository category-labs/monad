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

set(BLST_SOURCE_DIR "${PROJECT_SOURCE_DIR}/third_party/blst")

enable_language(ASM)

add_library(blst STATIC
    "${BLST_SOURCE_DIR}/build/assembly.S"
    "${BLST_SOURCE_DIR}/src/server.c")

target_include_directories(blst PUBLIC ${BLST_SOURCE_DIR}/bindings)

# The compilation options and defintions match what build.sh would do; if you
# upgrade libblst, ensure this is still the case
target_compile_options(blst PRIVATE -Wall -Wextra -Werror)
target_compile_definitions(blst PRIVATE __ADX__)
set_target_properties(blst PROPERTIES POSITION_INDEPENDENT_CODE ON)

add_library(blst::blst ALIAS blst)
