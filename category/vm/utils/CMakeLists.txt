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

add_library(monad-vm-utils OBJECT)

target_sources(monad-vm-utils PRIVATE
    "debug.cpp"
    "debug.hpp"
    "evmc_utils.cpp"
    "evmc_utils.hpp"
    "load_program.hpp"
    "lru_weight_cache.hpp"
    "rc_ptr.hpp"
    "parser.cpp"
    "parser.hpp"
    "scope_exit.hpp"
    "traits.hpp"

    # evm-as
    "evm-as.hpp"
    "evm-as/builder.hpp"
    "evm-as/compiler.cpp"
    "evm-as/compiler.hpp"
    "evm-as/instruction.hpp"
    "evm-as/resolver.hpp"
    "evm-as/validator.hpp"
    "evm-as/utils.hpp"
)

monad_compile_options(monad-vm-utils)

target_include_directories(monad-vm-utils
    PUBLIC ${CATEGORY_MAIN_DIR}
)

target_link_libraries(monad-vm-utils
    PUBLIC monad-vm::monad-vm-core
    PUBLIC monad-vm::monad-vm-runtime
    PRIVATE monad-vm::monad-vm-evm
)

add_library(monad-vm::monad-vm-utils ALIAS monad-vm-utils)
