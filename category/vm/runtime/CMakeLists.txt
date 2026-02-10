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

enable_language(ASM)

add_library(monad-vm-runtime OBJECT)

target_sources(monad-vm-runtime PRIVATE
    "allocator.hpp"
    "allocator.cpp"
    "cached_allocator.hpp"
    "bin.hpp"
    "call.hpp"
    "call.cpp"
    "context.S"
    "context.cpp"
    "create.hpp"
    "create.cpp"
    "data.hpp"
    "data.cpp"
    "detail.hpp"
    "environment.hpp"
    "environment.cpp"
    "exit.S"
    "exit.cpp"
    "keccak.hpp"
    "keccak.cpp"
    "log.hpp"
    "log.cpp"
    "math.S"
    "math.hpp"
    "memory.hpp"
    "memory.cpp"
    "runtime.hpp"
    "selfdestruct.hpp"
    "selfdestruct.cpp"
    "storage.cpp"
    "storage.hpp"
    "storage_costs.hpp"
    "transmute.S"
    "transmute.hpp"
    "types.hpp"
)

monad_compile_options(monad-vm-runtime)

target_include_directories(monad-vm-runtime
    PUBLIC ${CATEGORY_MAIN_DIR}
)

target_link_libraries(monad-vm-runtime
    PUBLIC evmc::evmc
    PUBLIC ethash::keccak
    PUBLIC intx::intx
    PUBLIC monad-vm::monad-vm-core
    PUBLIC monad-vm::monad-vm-evm
)

add_library(monad-vm::monad-vm-runtime ALIAS monad-vm-runtime)
