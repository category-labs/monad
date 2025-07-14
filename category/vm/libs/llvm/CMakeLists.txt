enable_language(ASM)

option(MONAD_VM_LLVM_DEBUG "Trace instructions executed by llvm backend" OFF)

# This option causes any binary that runs the Monad baseline interpreter to
# print a CSV-formatted summary of opcode executions when it exits. This code is
# not thread-safe and should only be enabled in appropriate benchmarking
# contexts, never in production.
option(MONAD_VM_LLVM_STATS "Print opcode statistics on program exit" OFF)

add_library(monad-vm-llvm STATIC)

monad_link_llvm(monad-vm-llvm)

target_sources(monad-vm-llvm PRIVATE
  "src/monad/vm/llvm/entry.S"
  "src/monad/vm/llvm/execute.cpp"
  "src/monad/vm/llvm/execute.hpp"
  "src/monad/vm/llvm/emitter.hpp"
  "src/monad/vm/llvm/virtual_stack.hpp"
  "src/monad/vm/llvm/llvm.cpp"
  "src/monad/vm/llvm/llvm.hpp"
  "src/monad/vm/llvm/llvm_state.hpp"
)

monad_compile_options(monad-vm-llvm)

if(MONAD_VM_LLVM_DEBUG)
  target_compile_definitions(monad-vm-llvm PRIVATE MONAD_VM_LLVM_DEBUG)
endif()

if(MONAD_VM_LLVM_STATS)
  target_compile_definitions(monad-vm-LLVM PRIVATE MONAD_VM_LLVM_STATS)
endif()

target_include_directories(monad-vm-llvm
    PUBLIC src/
)

target_link_libraries(monad-vm-llvm
    PUBLIC intx::intx
    PUBLIC evmc::evmc
    PUBLIC monad-vm::monad-vm-evm
    PUBLIC monad-vm::monad-vm-runtime
    PUBLIC monad-vm::monad-vm-utils
    PUBLIC monad-vm::monad-vm-compiler
    PRIVATE monad-vm::monad-vm-core
)

add_library(monad-vm::monad-vm-llvm ALIAS monad-vm-llvm)
