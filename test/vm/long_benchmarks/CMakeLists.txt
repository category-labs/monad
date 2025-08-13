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

add_executable(long-benchmarks)
target_sources(long-benchmarks
    PRIVATE
        long-benchmarks.cpp
        code_0a743ba7304efcc9e384ece9be7631e2470e401e.hpp
        code_49206861766520746f6f206d7563682074696d65.hpp
        code_c917e98213a05d271adc5d93d2fee6c1f1006f75.hpp
        code_f529c70db0800449ebd81fbc6e4221523a989f05.hpp
        code_snailtracer.hpp
)
target_include_directories(long-benchmarks
    PRIVATE "${TOP_CURRENT_BINARY_DIR}/test"
    PRIVATE "${TEST_DATA_DIR}/unit/common/include"
)
monad_compile_options(long-benchmarks)

target_link_libraries(long-benchmarks
    PRIVATE benchmark::benchmark
    PRIVATE blockchain-test-vm
    PRIVATE evmone::state
    PRIVATE evmone::statetestutils
    PRIVATE evmone-blockchaintest-lib
    PRIVATE nlohmann_json::nlohmann_json
    PRIVATE monad_execution
)

# TODO(BSC): fix this via evmone
target_include_directories(long-benchmarks
  PRIVATE "${ROOT_DIRECTORY}/third_party/evmone/test/state"
  PRIVATE "${ROOT_DIRECTORY}/third_party/evmone/test/statetest"
)
