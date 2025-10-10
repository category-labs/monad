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
#include <category/vm/evm/traits.hpp>
#include <category/vm/host.hpp>
#include <category/vm/interpreter/execute.hpp>
#include <category/vm/runtime/allocator.hpp>
#include <category/vm/utils/debug.hpp>

namespace monad::vm
{
    constexpr auto counts_format_string =
        ",execute_intercode_calls={},execute_native_entrypoint_"
        "calls={},execute_raw_calls={}";

    struct VmStats
    {
        std::atomic<uint64_t> execute_intercode_call_count_per_block_{0};
        std::atomic<uint64_t> execute_native_entrypoint_call_count_per_block_{
            0};
        std::atomic<uint64_t> execute_raw_call_count_per_block_{0};
        std::atomic<uint64_t> execute_intercode_call_count_{0};
        std::atomic<uint64_t> execute_native_entrypoint_call_count_{0};
        std::atomic<uint64_t> execute_raw_call_count_{0};

        void event_execute_intercode() noexcept
        {
            if constexpr (utils::collect_monad_compiler_hot_path_stats) {
                execute_intercode_call_count_.fetch_add(
                    1, std::memory_order_release);
                execute_intercode_call_count_per_block_.fetch_add(
                    1, std::memory_order_release);
            }
        }

        void event_execute_native_entrypoint() noexcept
        {
            if constexpr (utils::collect_monad_compiler_hot_path_stats) {
                execute_native_entrypoint_call_count_.fetch_add(
                    1, std::memory_order_release);
                execute_native_entrypoint_call_count_per_block_.fetch_add(
                    1, std::memory_order_release);
            }
        }

        void event_execute_bytecode() noexcept
        {
            if constexpr (utils::collect_monad_compiler_hot_path_stats) {
                execute_raw_call_count_.fetch_add(1, std::memory_order_release);
                execute_raw_call_count_per_block_.fetch_add(
                    1, std::memory_order_release);
            }
        }

        void reset_block_counts() noexcept
        {
            if constexpr (utils::collect_monad_compiler_hot_path_stats) {
                execute_intercode_call_count_per_block_.store(
                    0, std::memory_order_release);
                execute_native_entrypoint_call_count_per_block_.store(
                    0, std::memory_order_release);
                execute_raw_call_count_per_block_.store(
                    0, std::memory_order_release);
            }
        }

        [[nodiscard]]
        std::string print_and_reset_block_counts()
        {
            if constexpr (utils::collect_monad_compiler_hot_path_stats) {
                std::string str = std::format(
                    counts_format_string,
                    execute_intercode_call_count_per_block_.load(
                        std::memory_order_acquire),
                    execute_native_entrypoint_call_count_per_block_.load(
                        std::memory_order_acquire),
                    execute_raw_call_count_per_block_.load(
                        std::memory_order_acquire));
                reset_block_counts();
                return str;
            }
            else {
                return "";
            }
        }

        std::string print_total_counts() const
        {
            if constexpr (utils::collect_monad_compiler_hot_path_stats) {
                return std::format(
                    counts_format_string,
                    execute_intercode_call_count_.load(
                        std::memory_order_acquire),
                    execute_native_entrypoint_call_count_.load(
                        std::memory_order_acquire),
                    execute_raw_call_count_.load(std::memory_order_acquire));
            }
            else {
                return "";
            }
        }
    };

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

        runtime::EvmStackAllocator &stack_allocator()
        {
            return stack_allocator_;
        }

        runtime::EvmMemoryAllocator &memory_allocator()
        {
            return memory_allocator_;
        };

        /// Execute varcode. The function will execute the nativecode in
        /// the varcode if set. Otherwise execute the intercode with
        /// interpreter and potentially start async compilation.
        template <Traits traits>
        evmc::Result execute(
            Host &host, evmc_message const *msg, evmc::bytes32 const &code_hash,
            SharedVarcode const &vcode);

        /// Execute the bytecode `code` with interpreter.
        template <Traits traits>
        evmc::Result execute_bytecode(
            Host &host, evmc_message const *msg, std::span<uint8_t const> code);

        /// Like `execute`, but without stack unwind support.
        template <Traits traits>
        evmc::Result execute_raw(
            evmc_host_interface const *host, evmc_host_context *host_ctx,
            evmc_message const *msg, evmc::bytes32 const &code_hash,
            SharedVarcode const &vcode);

        /// Like `execute_bytecode`, but without stack unwind support.
        template <Traits traits>
        evmc::Result execute_bytecode_raw(
            evmc_host_interface const *host, evmc_host_context *host_ctx,
            evmc_message const *msg, std::span<uint8_t const> code);

        /// Execute with interpreter, without stack unwind support.
        template <Traits traits>
        evmc::Result execute_intercode_raw(
            evmc_host_interface const *host, evmc_host_context *host_ctx,
            evmc_message const *msg, SharedIntercode const &icode);

        /// Execute the entrypoint, without stack unwind support.
        evmc::Result execute_native_entrypoint_raw(
            evmc_host_interface const *, evmc_host_context *,
            evmc_message const *, SharedIntercode const &,
            compiler::native::entrypoint_t);

        [[nodiscard]]
        std::string print_and_reset_block_counts()
        {
            return stats_.print_and_reset_block_counts();
        }

        std::string print_total_counts() const
        {
            return stats_.print_total_counts();
        }

        std::string print_compiler_stats() const
        {
            return compiler_.print_stats();
        }

    private:
        template <Traits traits>
        evmc::Result execute_impl(
            runtime::Context &rt_ctx, evmc::bytes32 const &code_hash,
            SharedVarcode const &vcode);

        template <Traits traits>
        evmc::Result execute_bytecode_impl(
            runtime::Context &rt_ctx, std::span<uint8_t const> code);

        template <Traits traits>
        evmc::Result execute_intercode_impl(
            runtime::Context &rt_ctx, SharedIntercode const &icode);

        evmc::Result execute_native_entrypoint_impl(
            runtime::Context &, compiler::native::entrypoint_t);

        VmStats stats_;
    };
}
