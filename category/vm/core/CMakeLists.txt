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

enable_language(C)

add_library(monad-vm-core OBJECT)

target_sources(monad-vm-core PRIVATE
    "assert.cpp"
    "assert.h"
    "cases.hpp"
)

monad_compile_options(monad-vm-core)

target_include_directories(monad-vm-core
    PUBLIC ${CATEGORY_MAIN_DIR}
)

add_library(monad-vm::monad-vm-core ALIAS monad-vm-core)
