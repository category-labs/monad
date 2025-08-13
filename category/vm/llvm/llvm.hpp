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

#pragma once

#include <category/vm/runtime/allocator.hpp>

namespace monad::vm::llvm
{
    struct LLVMState; // forward declaration so we don't have to pull in all the
                      // LLVM includes

    class VM
    {
        runtime::EvmStackAllocator stack_allocator_;
        runtime::EvmMemoryAllocator memory_allocator_;
        std::unordered_map<std::string, std::shared_ptr<LLVMState>>
            cached_llvm_code_;

    public:
        explicit VM(
            std::size_t max_stack_cache_byte_size =
                runtime::EvmStackAllocator::DEFAULT_MAX_CACHE_BYTE_SIZE,
            std::size_t max_memory_cache_byte_size =
                runtime::EvmMemoryAllocator::DEFAULT_MAX_CACHE_BYTE_SIZE);
        evmc::Result execute_llvm(
            evmc_revision rev, evmc_host_interface const *host,
            evmc_host_context *context, evmc_message const *msg,
            uint8_t const *code, size_t code_size,
            evmc::bytes32 const &code_hash);

        std::shared_ptr<LLVMState> cache_llvm(
            evmc_revision rev, uint8_t const *code, size_t code_size,
            evmc::bytes32 const &code_hash);
    };
}
