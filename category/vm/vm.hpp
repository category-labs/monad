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

#include <category/vm/code.hpp>
#include <category/vm/compiler.hpp>
#include <category/vm/compiler/ir/x86.hpp>
#include <category/vm/runtime/allocator.hpp>

namespace monad::vm
{

    class VM
    {
        Compiler compiler_;
        CompilerConfig compiler_config_;
        runtime::EvmStackAllocator stack_allocator_;
        runtime::EvmMemoryAllocator memory_allocator_;

    public:
        explicit VM(
            bool enable_async = true,
            std::size_t max_stack_cache_byte_size =
                runtime::EvmStackAllocator::DEFAULT_MAX_CACHE_BYTE_SIZE,
            std::size_t max_memory_cache_byte_size =
                runtime::EvmMemoryAllocator::DEFAULT_MAX_CACHE_BYTE_SIZE);

        std::optional<SharedVarcode>
        find_varcode(evmc::bytes32 const &code_hash)
        {
            return compiler_.find_varcode(code_hash);
        }

        SharedVarcode try_insert_varcode(
            evmc::bytes32 const &code_hash, SharedIntercode const &icode)
        {
            return compiler_.try_insert_varcode(code_hash, icode);
        }

        Compiler &compiler()
        {
            return compiler_;
        }

        CompilerConfig const &compiler_config()
        {
            return compiler_config_;
        }

        /// Execute varcode. The function will execute the nativecode in
        /// the varcode if set, and otherwise start async compilation and
        /// execute the intercode with interpreter.
        evmc::Result execute(
            evmc_revision, evmc_host_interface const *, evmc_host_context *,
            evmc_message const *, evmc::bytes32 const &code_hash,
            SharedVarcode const &);

        /// Execute the raw `code` with interpreter.
        evmc::Result execute_raw(
            evmc_revision, evmc_host_interface const *, evmc_host_context *,
            evmc_message const *, std::span<uint8_t const> code);

        /// Execute the intercode with interpreter.
        evmc::Result execute_intercode(
            evmc_revision, evmc_host_interface const *, evmc_host_context *,
            evmc_message const *, SharedIntercode const &);

        /// Execute the entrypoint`.
        evmc::Result execute_native_entrypoint(
            evmc_host_interface const *, evmc_host_context *,
            evmc_message const *, SharedIntercode const &,
            compiler::native::entrypoint_t);
    };
}
