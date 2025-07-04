enable_language(ASM)

option(MONAD_VM_INTERPRETER_DEBUG "Trace instructions executed by interpreter" OFF)

# This option causes any binary that runs the Monad baseline interpreter to
# print a CSV-formatted summary of opcode executions when it exits. This code is
# not thread-safe and should only be enabled in appropriate benchmarking
# contexts, never in production.
option(MONAD_VM_INTERPRETER_STATS "Print opcode statistics on program exit" OFF)

add_library(monad-vm-interpreter STATIC)

target_sources(monad-vm-interpreter PRIVATE
  "src/monad/vm/interpreter/call_runtime.hpp"
  "src/monad/vm/interpreter/debug.hpp"
  "src/monad/vm/interpreter/entry.S"
  "src/monad/vm/interpreter/execute.cpp"
  "src/monad/vm/interpreter/execute.hpp"
  "src/monad/vm/interpreter/instruction_stats.cpp"
  "src/monad/vm/interpreter/instruction_stats.hpp"
  "src/monad/vm/interpreter/instruction_table.hpp"
  "src/monad/vm/interpreter/instructions_fwd.hpp"
  "src/monad/vm/interpreter/intercode.cpp"
  "src/monad/vm/interpreter/intercode.hpp"
  "src/monad/vm/interpreter/push.hpp"
  "src/monad/vm/interpreter/stack.hpp"
  "src/monad/vm/interpreter/types.hpp"
)

monad_compile_options(monad-vm-interpreter)

# Use -Og for debug build to reduce stack usage.
target_compile_options(monad-vm-interpreter PRIVATE $<$<CONFIG:Debug>:-Og>)

# This is a workaround for a change made to LLVM between versions 18 and 19:
# https://github.com/llvm/llvm-project/pull/78582
#
# The change in question restricts the default maximum predecessors and
# successors that a basic block can have if it is to be duplicated (rather than
# being shared). This affects the dispatch table of the interpreter by causing
# the "load next instruction, indirect jump" block tail to be emitted as a
# single shared block rather than being inlined into each opcode's dispatch
# block. Doing so slows the interpreter down when compiled with Clang 19.
# Because the LLVM change in question is for _compiler_ performance rather than
# _runtime_ performance, we can safely disable the pessimisation by setting this
# flag to a value we know to be large enough for our dispatch table.
target_compile_options(
  monad-vm-interpreter
  PRIVATE $<$<COMPILE_LANG_AND_ID:CXX,Clang>:-mllvm -tail-dup-pred-size=256>)

if(MONAD_VM_INTERPRETER_DEBUG)
  target_compile_definitions(monad-vm-interpreter PRIVATE MONAD_VM_INTERPRETER_DEBUG)
endif()

if(MONAD_VM_INTERPRETER_STATS)
  target_compile_definitions(monad-vm-interpreter PRIVATE MONAD_VM_INTERPRETER_STATS)
endif()

target_include_directories(monad-vm-interpreter
    PUBLIC src/
)

target_link_libraries(monad-vm-interpreter
    PUBLIC intx::intx
    PUBLIC evmc::evmc
    PUBLIC monad-vm::monad-vm-evm
    PUBLIC monad-vm::monad-vm-runtime
    PUBLIC monad-vm::monad-vm-utils
    PRIVATE monad-vm::monad-vm-core
)

add_library(monad-vm::monad-vm-interpreter ALIAS monad-vm-interpreter)
