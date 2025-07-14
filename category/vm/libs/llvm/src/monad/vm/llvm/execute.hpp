#pragma once

#include <monad/vm/llvm/llvm_state.hpp>

#include <monad/vm/runtime/types.hpp>
#include <monad/vm/runtime/uint256.hpp>

namespace monad::vm::llvm
{
    using namespace monad::vm::runtime;

    void execute(LLVMState &llvm, Context &, uint256_t *);
    std::shared_ptr<LLVMState>
    compile(evmc_revision rev, std::span<uint8_t const> code);
}
