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

# Compiler Blockchain Tests

add_executable(compiler-blockchain-tests)
target_sources(compiler-blockchain-tests
    PRIVATE
        compiler_blockchain_tests.cpp
)
target_include_directories(compiler-blockchain-tests
    PRIVATE "${TOP_CURRENT_BINARY_DIR}/test"
    PRIVATE "${TEST_DATA_DIR}/unit/common/include"
)
monad_compile_options(compiler-blockchain-tests)

target_link_libraries(compiler-blockchain-tests
    PRIVATE blockchain-test-vm
    PRIVATE evmone-blockchaintest-lib
    PRIVATE monad_execution
)

# Interpreter Blockchain Tests

add_executable(interpreter-blockchain-tests)
target_sources(interpreter-blockchain-tests
    PRIVATE
        interpreter_blockchain_tests.cpp
)
target_include_directories(interpreter-blockchain-tests
    PRIVATE "${TOP_CURRENT_BINARY_DIR}/test"
    PRIVATE "${TEST_DATA_DIR}/unit/common/include"
)
monad_compile_options(interpreter-blockchain-tests)

target_link_libraries(interpreter-blockchain-tests
    PRIVATE blockchain-test-vm
    PRIVATE evmone-blockchaintest-lib
    PRIVATE monad_execution
)

# LLVM Blockchain Tests

if(MONAD_COMPILER_LLVM)
    add_executable(llvm-blockchain-tests)

    target_sources(llvm-blockchain-tests
        PRIVATE
            llvm_blockchain_tests.cpp
    )

    target_include_directories(llvm-blockchain-tests
        PRIVATE "${TOP_CURRENT_BINARY_DIR}/test"
        PRIVATE "${TEST_DATA_DIR}/unit/common/include"
    )

    monad_compile_options(llvm-blockchain-tests)

    target_link_libraries(llvm-blockchain-tests
        PRIVATE blockchain-test-vm
        PRIVATE monad-vm::monad-vm-llvm
        PRIVATE evmone-blockchaintest-lib
        PRIVATE monad_execution
    )
endif()

# Coverage

if(MONAD_COMPILER_COVERAGE)
    target_compile_options(interpreter-blockchain-tests PRIVATE -coverage)
    target_link_options(interpreter-blockchain-tests PRIVATE -coverage)
    target_compile_options(compiler-blockchain-tests PRIVATE -coverage)
    target_link_options(compiler-blockchain-tests PRIVATE -coverage)
    if(MONAD_COMPILER_LLVM)
        target_compile_options(llvm-blockchain-tests PRIVATE -coverage)
        target_link_options(llvm-blockchain-tests PRIVATE -coverage)
    endif()
endif()
