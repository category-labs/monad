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

#include <category/vm/core/assert.h>
#include <category/vm/runtime/allocator.hpp>
#include <category/vm/runtime/bin.hpp>
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/uint256.hpp>

#include <evmc/evmc.hpp>

#include <cstddef>
#include <span>
#include <type_traits>
#include <variant>
#include <vector>

namespace monad::vm::runtime
{
    enum class StatusCode : uint64_t
    {
        Success = 0,
        Revert,
        Error,
        OutOfGas,
    };

    struct alignas(uint64_t) Result
    {
        uint8_t offset[32];
        uint8_t size[32];
        StatusCode status;
    };

    struct Environment
    {
        std::uint32_t evmc_flags;
        std::int32_t depth;
        evmc::address recipient;
        evmc::address sender;
        evmc::bytes32 value;
        evmc::bytes32 create2_salt;

        std::uint8_t const *input_data;
        std::uint8_t const *code;
        std::uint8_t const *return_data;

        std::uint32_t input_data_size;
        std::uint32_t code_size;
        std::size_t return_data_size;

        evmc_tx_context tx_context;

        ~Environment()
        {
            std::free(const_cast<uint8_t *>(return_data));
        }

        [[gnu::always_inline]]
        void set_return_data(
            std::uint8_t const *output_data, std::size_t output_size)
        {
            MONAD_VM_DEBUG_ASSERT(return_data_size == 0);
            return_data = output_data;
            return_data_size = output_size;
        }

        [[gnu::always_inline]]
        void clear_return_data()
        {
            std::free(const_cast<uint8_t *>(return_data));
            return_data = nullptr;
            return_data_size = 0;
        }
    };

    struct Memory
    {
        EvmMemoryAllocator allocator_;
        std::uint32_t size;
        std::uint32_t capacity;
        std::uint8_t *data;
        std::int64_t cost;

        static constexpr auto initial_capacity = 4096;

        static constexpr auto offset_bits = 28;

        using Offset = Bin<offset_bits>;

        Memory() = delete;

        explicit Memory(EvmMemoryAllocator allocator)
            : allocator_{allocator}
            , size{}
            , capacity{initial_capacity}
            , data{allocator_.aligned_alloc_cached()}
            , cost{}
        {
            memset(data, 0, capacity);
        }

        Memory(Memory &&m) noexcept
            : allocator_{m.allocator_}
            , size{m.size}
            , capacity{m.capacity}
            , data{m.data}
            , cost{m.cost}
        {
            m.clear();
        }

        Memory &operator=(Memory &&m) noexcept
        {
            dealloc(data);

            size = m.size;
            capacity = m.capacity;
            data = m.data;
            cost = m.cost;

            m.clear();
            return *this;
        }

        Memory(Memory const &) = delete;

        Memory &operator=(Memory const &) = delete;

        ~Memory()
        {
            dealloc(data);
        }

        [[gnu::always_inline]]
        void clear()
        {
            size = 0;
            capacity = 0;
            data = nullptr;
            cost = 0;
        }

        [[gnu::always_inline]]
        void dealloc(uint8_t *d)
        {
            if (capacity == initial_capacity) {
                allocator_.free_cached(d);
            }
            else {
                std::free(d);
            }
        }
    };

    struct Context
    {
        static Context from(
            EvmMemoryAllocator mem_alloc, evmc_host_interface const *host,
            evmc_host_context *context, evmc_message const *msg,
            std::span<std::uint8_t const> code) noexcept;

        static Context empty() noexcept;

        evmc_host_interface const *host;
        evmc_host_context *context;

        std::int64_t gas_remaining;
        std::int64_t gas_refund;

        Environment env;

        Result result = {};

        Memory memory;

        void *exit_stack_ptr = nullptr;
        bool is_stack_unwinding_active = false;

        [[gnu::always_inline]]
        constexpr void deduct_gas(std::int64_t const gas) noexcept
        {
            gas_remaining -= gas;
            if (MONAD_VM_UNLIKELY(gas_remaining < 0)) {
                exit(StatusCode::OutOfGas);
            }
        }

        [[gnu::always_inline]]
        constexpr void deduct_gas(Bin<32> const gas) noexcept
        {
            return deduct_gas(*gas);
        }

        [[gnu::always_inline]]
        static constexpr int64_t
        memory_cost_from_word_count(Bin<32> const word_count) noexcept
        {
            auto const c = static_cast<uint64_t>(*word_count);
            return static_cast<int64_t>((c * c) / 512 + (3 * c));
        }

        void increase_capacity(uint32_t old_size, Bin<31> new_size);

        void expand_memory(Bin<30> min_size)
        {
            if (memory.size < *min_size) {
                auto const wsize = shr_ceil<5>(min_size);
                std::int64_t const new_cost =
                    memory_cost_from_word_count(wsize);
                Bin<31> const new_size = shl<5>(wsize);
                MONAD_VM_DEBUG_ASSERT(new_cost >= memory.cost);
                std::int64_t const expansion_cost = new_cost - memory.cost;
                // Gas check before increasing capacity:
                deduct_gas(expansion_cost);
                uint32_t const old_size = memory.size;
                memory.size = *new_size;
                memory.cost = new_cost;
                if (memory.capacity < *new_size) {
                    increase_capacity(old_size, new_size);
                }
            }
        }

        [[gnu::always_inline]]
        Memory::Offset get_memory_offset(uint256_t const &offset)
        {
            if (MONAD_VM_UNLIKELY(
                    !is_bounded_by_bits<Memory::offset_bits>(offset))) {
                exit(StatusCode::OutOfGas);
            }
            return Memory::Offset::unsafe_from(static_cast<uint32_t>(offset));
        }

        [[gnu::always_inline]]
        void propagate_stack_unwind() noexcept
        {
            if (MONAD_VM_UNLIKELY(is_stack_unwinding_active)) {
                stack_unwind();
            }
        }

        void stack_unwind [[noreturn]] () noexcept;

        void exit [[noreturn]] (StatusCode code) noexcept;

        evmc::Result copy_to_evmc_result();

    private:
        std::variant<std::span<std::uint8_t const>, evmc_status_code>
        copy_result_data();
    };

    // Update context.S accordingly if these offsets change:
    static_assert(offsetof(Context, gas_remaining) == 16);
    static_assert(offsetof(Context, memory) == 512);
    static_assert(offsetof(Memory, size) == 8);
    static_assert(offsetof(Memory, capacity) == 12);
    static_assert(offsetof(Memory, cost) == 24);

    constexpr auto context_offset_gas_remaining =
        offsetof(Context, gas_remaining);
    constexpr auto context_offset_exit_stack_ptr =
        offsetof(Context, exit_stack_ptr);
    constexpr auto context_offset_env_recipient =
        offsetof(Context, env) + offsetof(Environment, recipient);
    constexpr auto context_offset_env_sender =
        offsetof(Context, env) + offsetof(Environment, sender);
    constexpr auto context_offset_env_value =
        offsetof(Context, env) + offsetof(Environment, value);
    constexpr auto context_offset_env_code_size =
        offsetof(Context, env) + offsetof(Environment, code_size);
    constexpr auto context_offset_env_input_data =
        offsetof(Context, env) + offsetof(Environment, input_data);
    constexpr auto context_offset_env_input_data_size =
        offsetof(Context, env) + offsetof(Environment, input_data_size);
    constexpr auto context_offset_env_return_data_size =
        offsetof(Context, env) + offsetof(Environment, return_data_size);
    constexpr auto context_offset_env_tx_context_origin =
        offsetof(Context, env) + offsetof(Environment, tx_context) +
        offsetof(evmc_tx_context, tx_origin);
    constexpr auto context_offset_env_tx_context_tx_gas_price =
        offsetof(Context, env) + offsetof(Environment, tx_context) +
        offsetof(evmc_tx_context, tx_gas_price);
    constexpr auto context_offset_env_tx_context_block_gas_limit =
        offsetof(Context, env) + offsetof(Environment, tx_context) +
        offsetof(evmc_tx_context, block_gas_limit);
    constexpr auto context_offset_env_tx_context_block_coinbase =
        offsetof(Context, env) + offsetof(Environment, tx_context) +
        offsetof(evmc_tx_context, block_coinbase);
    constexpr auto context_offset_env_tx_context_block_timestamp =
        offsetof(Context, env) + offsetof(Environment, tx_context) +
        offsetof(evmc_tx_context, block_timestamp);
    constexpr auto context_offset_env_tx_context_block_number =
        offsetof(Context, env) + offsetof(Environment, tx_context) +
        offsetof(evmc_tx_context, block_number);
    constexpr auto context_offset_env_tx_context_block_prev_randao =
        offsetof(Context, env) + offsetof(Environment, tx_context) +
        offsetof(evmc_tx_context, block_prev_randao);
    constexpr auto context_offset_env_tx_context_chain_id =
        offsetof(Context, env) + offsetof(Environment, tx_context) +
        offsetof(evmc_tx_context, chain_id);
    constexpr auto context_offset_env_tx_context_block_base_fee =
        offsetof(Context, env) + offsetof(Environment, tx_context) +
        offsetof(evmc_tx_context, block_base_fee);
    constexpr auto context_offset_env_tx_context_blob_base_fee =
        offsetof(Context, env) + offsetof(Environment, tx_context) +
        offsetof(evmc_tx_context, blob_base_fee);
    constexpr auto context_offset_memory_size =
        offsetof(Context, memory) + offsetof(Memory, size);
    constexpr auto context_offset_memory_data =
        offsetof(Context, memory) + offsetof(Memory, data);
    constexpr auto context_offset_result_offset =
        offsetof(Context, result) + offsetof(Result, offset);
    constexpr auto context_offset_result_size =
        offsetof(Context, result) + offsetof(Result, size);
    constexpr auto context_offset_result_status =
        offsetof(Context, result) + offsetof(Result, status);

}

extern "C" void monad_vm_runtime_increase_capacity(
    monad::vm::runtime::Context *, uint32_t old_size,
    monad::vm::runtime::Bin<31> new_size);

extern "C" void monad_vm_runtime_increase_memory(
    monad::vm::runtime::Bin<30> min_size, monad::vm::runtime::Context *);

// Note: monad_vm_runtime_increase_memory_raw uses non-standard
// calling convention. Context is passed in rbx and new min
// memory size if passed in rdi. See context.S. Use the
// monad_vm_runtime_increase_memory function for a version
// using standard calling convention
extern "C" void monad_vm_runtime_increase_memory_raw();
