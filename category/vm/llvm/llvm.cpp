// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/vm/llvm/execute.hpp>
#include <category/vm/llvm/llvm.hpp>
#include <category/vm/llvm/llvm_state.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/runtime/uint256.hpp>
#include <category/vm/utils/evmc_utils.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <cstddef>
#include <cstdint>
#include <format>
#include <memory>
#include <span>
#include <string>

namespace monad::vm::llvm
{
    VM::VM(std::size_t max_stack_cache, std::size_t max_memory_cache)
        : stack_allocator_{max_stack_cache}
        , memory_allocator_{max_memory_cache}
    {
    }

    std::shared_ptr<LLVMState> VM::cache_llvm(
        evmc_revision rev, uint8_t const *code, size_t code_size,
        evmc::bytes32 const &code_hash)
    {
        auto code_hash_str = monad::vm::utils::hex_string(code_hash);
        std::string const hash_str =
            std::format("{}{}", (int)rev, code_hash_str);

        auto item = cached_llvm_code_.find(hash_str);
        if (item != cached_llvm_code_.end()) {
            return item->second;
        }

        auto ptr = monad::vm::llvm::compile(rev, {code, code_size});
        cached_llvm_code_.insert({hash_str, ptr});

        return ptr;
    }

    evmc::Result VM::execute_llvm(
        evmc_revision rev, evmc_host_interface const *host,
        evmc_host_context *context, evmc_message const *msg,
        uint8_t const *code, size_t code_size, evmc::bytes32 const &code_hash)
    {
        auto ctx = runtime::Context::from(
            memory_allocator_, host, context, msg, {code, code_size});

        auto const stack_ptr = stack_allocator_.allocate();
        uint256_t *evm_stack = reinterpret_cast<uint256_t *>(stack_ptr.get());

        auto llvm = cache_llvm(rev, code, code_size, code_hash);

        monad::vm::llvm::execute(*llvm, ctx, evm_stack);

        return ctx.copy_to_evmc_result();
    }

}
