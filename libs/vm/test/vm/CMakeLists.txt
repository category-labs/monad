# Testing VM

add_library(blockchain-test-vm STATIC)

if(MONAD_COMPILER_LLVM)
    monad_link_llvm(blockchain-test-vm)
    target_link_libraries(blockchain-test-vm
        PUBLIC monad-vm::monad-vm-llvm
    )
endif()

target_sources(blockchain-test-vm
    PRIVATE
        test_vm.hpp
        test_vm.cpp
)

target_link_libraries(blockchain-test-vm
    PUBLIC
        evmc::evmc
        monad-vm::monad-vm
        monad-vm::monad-vm-compiler
        monad-vm::monad-vm-interpreter
)

target_include_directories(blockchain-test-vm
    PUBLIC .
    PUBLIC "${ROOT_DIRECTORY}/third_party/evmone/test/state"
)
monad_compile_options(blockchain-test-vm)
