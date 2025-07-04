# Compiler Blockchain Tests

add_executable(compiler-blockchain-tests)
target_sources(compiler-blockchain-tests
    PRIVATE
        compiler_blockchain_tests.cpp
)
target_include_directories(compiler-blockchain-tests
    PRIVATE
        "${TOP_CURRENT_BINARY_DIR}/test"
)
monad_compile_options(compiler-blockchain-tests)

target_link_libraries(compiler-blockchain-tests
    blockchain-test-vm
    monad-vm::monad-vm
    monad-vm::monad-vm-compiler
    monad-vm::monad-vm-utils
    evmone-blockchaintest-lib)

# Interpreter Blockchain Tests

add_executable(interpreter-blockchain-tests)
target_sources(interpreter-blockchain-tests
    PRIVATE
        interpreter_blockchain_tests.cpp
)
target_include_directories(interpreter-blockchain-tests
    PRIVATE
        "${TOP_CURRENT_BINARY_DIR}/test"
)
monad_compile_options(interpreter-blockchain-tests)

target_link_libraries(interpreter-blockchain-tests
    blockchain-test-vm
    monad-vm::monad-vm-utils
    monad-vm::monad-vm-interpreter
    evmone-blockchaintest-lib)

# LLVM Blockchain Tests

if(MONAD_COMPILER_LLVM)
    add_executable(llvm-blockchain-tests)

    target_sources(llvm-blockchain-tests
        PRIVATE
            llvm_blockchain_tests.cpp
    )

    target_include_directories(llvm-blockchain-tests
        PRIVATE
            "${TOP_CURRENT_BINARY_DIR}/test"
    )

    monad_compile_options(llvm-blockchain-tests)

    target_link_libraries(llvm-blockchain-tests
        PRIVATE blockchain-test-vm
        PRIVATE monad-vm::monad-vm-llvm
        PRIVATE evmone-blockchaintest-lib
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
