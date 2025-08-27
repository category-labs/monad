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

add_library(monad-vm-evm OBJECT)

set_target_properties(monad-vm-evm PROPERTIES LINKER_LANGUAGE CXX)

target_sources(monad-vm-evm PRIVATE
    "chain.hpp"
    "delegation.cpp"
    "delegation.hpp"
    "opcodes.hpp"
    "opcodes_xmacro.hpp"
)

target_include_directories(monad-vm-evm
    PUBLIC ${CATEGORY_MAIN_DIR}
)

target_link_libraries(monad-vm-evm
    PUBLIC evmc::evmc
    PUBLIC monad-vm::monad-vm-core
)

monad_compile_options(monad-vm-evm)

add_library(monad-vm::monad-vm-evm ALIAS monad-vm-evm)
