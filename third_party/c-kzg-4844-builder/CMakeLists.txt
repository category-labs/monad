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

cmake_minimum_required(VERSION 3.20)
project(c-kzg-4844)

set(SUBMODULE_DIR ${THIRD_PARTY_DIR}/c-kzg-4844)

add_library(c-kzg-4844 STATIC)

target_sources(c-kzg-4844 PRIVATE
    "${SUBMODULE_DIR}/src/ckzg.c"
)

target_link_libraries(c-kzg-4844
    PRIVATE blst::blst
)

target_include_directories(c-kzg-4844
    PUBLIC ${SUBMODULE_DIR}/src
)

target_compile_options(c-kzg-4844 PRIVATE
    -Wall -Wextra -Werror -Wno-missing-braces -Wno-unused-parameter -Wno-format
)