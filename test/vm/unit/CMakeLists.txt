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

add_executable(vm-unit-tests
    async_compile_tests.cpp
    bin_tests.cpp
    compiler_tests.cpp
    evm_fixture.cpp
    evm_tests.cpp
    evm-as_tests.cpp
    monad_vm_interface_tests.cpp
    utils_tests.cpp
    uint256_tests.cpp
    rc_ptr_tests.cpp
    strongly_connected_components_tests.cpp
    transactional_unordered_map_tests.cpp
    subst_map_tests.cpp
    kind_tests.cpp
    unify_tests.cpp
    infer_tests.cpp
    type_check_tests.cpp
    stack_tests.cpp
    emitter_tests.cpp
    interpreter_tests.cpp
    lru_weight_cache_tests.cpp
    runtime/fixture.cpp
    runtime/transmute_tests.cpp
    runtime/math_tests.cpp
    runtime/memory_tests.cpp
    runtime/keccak_tests.cpp
    runtime/environment_tests.cpp
    runtime/storage_tests.cpp
    runtime/call_tests.cpp
    runtime/data_tests.cpp
    runtime/create_tests.cpp
)

if(MONAD_COMPILER_COVERAGE)
    target_compile_options(vm-unit-tests PRIVATE -coverage)
    target_link_options(vm-unit-tests PRIVATE -coverage)
endif()

monad_compile_options(vm-unit-tests)
target_link_libraries(vm-unit-tests
    PRIVATE evmone
    PRIVATE monad-vm::monad-vm-fuzzing
    PRIVATE GTest::gtest_main
    PRIVATE evmc::mocked_host
    PRIVATE monad_execution
)

target_include_directories(vm-unit-tests
    PRIVATE "${TOP_CURRENT_BINARY_DIR}/test"
    PRIVATE "${TEST_DATA_DIR}/unit/common/include"
)
