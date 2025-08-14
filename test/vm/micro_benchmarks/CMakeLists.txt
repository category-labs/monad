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

add_executable(vm-micro-benchmarks)
target_sources(vm-micro-benchmarks
    PRIVATE main.cpp
)
target_include_directories(vm-micro-benchmarks
    PRIVATE "${TOP_CURRENT_BINARY_DIR}/test"
)
monad_compile_options(vm-micro-benchmarks)

target_link_libraries(vm-micro-benchmarks
    PRIVATE blockchain-test-vm
    PRIVATE monad-vm::monad-vm-test-utils
    PRIVATE evmone::state
    PRIVATE evmone::statetestutils
    PRIVATE evmone-blockchaintest-lib
    PRIVATE monad_execution
)

target_include_directories(vm-micro-benchmarks
  PRIVATE "${CATEGORY_MAIN_DIR}/third_party"
)
