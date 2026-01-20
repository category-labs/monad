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

#include <category/core/runtime/non_temporal_memory.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/bin.hpp>
#include <category/vm/runtime/transmute.hpp>

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

        evmc_tx_context const *tx_context;

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
        // Size of the memory region for current call frame:
        std::uint32_t size;
        // Capacity of the memory region for current call frame:
        std::uint32_t capacity;
        // Start of memory region for current call frame:
        std::uint8_t *data;
        // Current accumulated memory cost for current call frame:
        std::int64_t cost;
        // Pointer to the beginning of the transaction wide memory:
        std::uint8_t *data_handle;
        // The `parent_capacity` is the original capacity (the capacity at
        // the beginning of the current call frame).
        std::uint32_t const parent_capacity;
        // The `parent_handle` is a pointer to the original transaction wide
        // memory (the transaction wide memory at the beginning of the
        // current call frame).
        // The `parent_handle` is kept around to allow for lazily freeing the
        // memory pointed to by `parent_handle`. This memory is lazily freed,
        // because the call data for the current call frame is potentially a
        // pointer into the `parent_handle` memory.
        std::uint8_t *const parent_handle;

        static constexpr auto offset_bits = 28;

        enum class Version
        {
            V1,
            MIP3
        };

        using Offset = Bin<offset_bits>;

        Memory() = delete;

        explicit Memory(std::uint8_t *han, std::uint8_t *dat, std::uint32_t cap)
            : size{}
            , capacity{cap}
            , data{dat}
            , cost{}
            , data_handle{han}
            , parent_capacity{cap}
            , parent_handle{han}
        {
            MONAD_VM_DEBUG_ASSERT(han != nullptr);
            MONAD_VM_DEBUG_ASSERT(dat != nullptr);
        }

        Memory(Memory &&m) = delete;
        Memory &operator=(Memory &&m) = delete;
        Memory(Memory const &) = delete;
        Memory &operator=(Memory const &) = delete;

        ~Memory()
        {
            // Under the production circumstances, this destructor is not
            // necessary, because the `Context::return_to` function will take
            // care of clearing and freeing memory. However relying on calling
            // `Context::return_to` seems unreasonable in general.
            if (MONAD_VM_UNLIKELY(data_handle)) {
                MONAD_VM_ASSERT(size <= capacity);
                MONAD_VM_ASSERT(data == data_handle);
                clear();
            }
        }

        [[gnu::always_inline]]
        Bin<30> parent_total_size() const
        {
            MONAD_VM_DEBUG_ASSERT(data >= data_handle);

            auto const x = static_cast<std::uintptr_t>(data - data_handle);

            MONAD_VM_DEBUG_ASSERT((x & 31) == 0);

            // The following check is a non-debug assertion, because it is not
            // an internal invariant, and not part of the fast path. The check
            // will hold if transaction gas limit is not larger than 2 billion
            // and max call depth is 1024. To see this, notice that the
            // maximum amount of memory usage is achieved by evenly splitting
            // memory consumption across the maximal 1024 call frames. By
            // splitting Bin<30>::upper = 2^30 - 1 into 1024 call frames, each
            // call frame will use
            //   (2^30 - 1) / 1024 > 2^20 - 1 bytes
            // of memory.
            // Therefore if the total memory size of the parent call frame is
            // larger than Bin<30>::upper, the transaction has accessed a
            // memory index larger than Bin<30>::upper. Hence if MIP-3 is not
            // active, a lower bound on current gas consumption is
            //   max_call_depth * memory_cost_from_word_count<...>(2^20 - 1)
            //   = 1024 * ((c * c) / 512 + (3 * c))
            //   > 2 billion
            //   for c = floor((2^20 - 1) / 32).
            // If MIP-3 is active, then parent memory size is automatically
            // upper bounded by the 8 MB transaction peak memory limit.
            // This means that more than 2 billion gas must have been consumed
            // already by the current transaction for the following assertion
            // to fail:
            MONAD_VM_ASSERT(x <= Bin<30>::upper);

            return Bin<30>::unsafe_from(static_cast<std::uint32_t>(x));
        }

        [[gnu::always_inline]]
        void clear()
        {
            if (MONAD_VM_LIKELY(parent_handle == data_handle)) {
                non_temporal_bzero(data_handle, size);
            }
            else {
                non_temporal_bzero(parent_handle, parent_capacity);
                std::free(data_handle);
            }
        }

        [[gnu::always_inline]]
        void release()
        {
            if (MONAD_VM_UNLIKELY(data_handle != parent_handle)) {
                // Only free if data_handle is not the parent_handle. The
                // parent_handle is potentially used for call data.
                // Note that data_handle will never be the initial memory
                // handle in this case. This is because if the data_handle
                // is the initial memory handle, then it is necessarily also
                // the parent_handle.
                std::free(data_handle);
            }
        }
    };

    struct Context
    {
        static Context from(
            evmc_host_interface const *host, evmc_host_context *context,
            evmc_message const *msg,
            std::span<std::uint8_t const> code) noexcept;

        static Context empty(
            std::uint8_t *const memory_handle,
            std::uint32_t memory_capacity) noexcept;

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

        template <Traits traits>
        [[gnu::always_inline]]
        static constexpr int64_t
        memory_cost_from_word_count(Bin<32> const word_count) noexcept
        {
            // The implementation of `parent_total_size` depends on a large
            // expansion cost for V1 memory version and depends on a small
            // fixed memory limit for MIP-3 memory version.
            if constexpr (traits::mip_3_active()) {
                // MIP-3 memory version
                return static_cast<int64_t>(*word_count >> 1);
            }
            else {
                // V1 memory version
                auto const c = static_cast<uint64_t>(*word_count);
                return static_cast<int64_t>((c * c) / 512 + (3 * c));
            }
        }

        [[gnu::always_inline]]
        static constexpr Bin<25>
        memory_size_to_word_count(Bin<29> const mem_size) noexcept
        {
            return shr_ceil<5>(mem_size);
        }

        [[gnu::always_inline]]
        static constexpr Bin<30>
        word_count_to_memory_size(Bin<25> word_count) noexcept
        {
            return shl<5>(word_count);
        }

        template <Traits traits>
        [[gnu::always_inline]]
        bool is_memory_size_in_bound(Bin<30> mem_size)
        {
            if constexpr (traits::mip_3_active()) {
                Bin<31> const total_size =
                    mem_size + memory.parent_total_size();
                constexpr uint32_t max_total_size = 0x800000; // 8MB
                return *total_size <= max_total_size;
            }
            return true;
        }

        void increase_capacity(uint32_t old_size, Bin<30> new_size);

        template <Traits traits>
        void expand_memory(Bin<29> min_size)
        {
            if (memory.size < *min_size) {
                auto const word_count = memory_size_to_word_count(min_size);
                auto const new_cost =
                    memory_cost_from_word_count<traits>(word_count);
                Bin<30> const new_size = word_count_to_memory_size(word_count);

                // Bound check before increasing size or capacity:
                if (MONAD_VM_UNLIKELY(
                        !is_memory_size_in_bound<traits>(new_size))) {
                    // Return out-of-gas error code, similar to when the
                    // `get_memory_offset` functions fails.
                    exit(StatusCode::OutOfGas);
                }

                MONAD_VM_DEBUG_ASSERT(new_cost >= memory.cost);
                std::int64_t const expansion_cost = new_cost - memory.cost;

                // Gas check before increasing size or capacity:
                deduct_gas(expansion_cost);
                uint32_t const old_size = memory.size;
                memory.size = *new_size;
                memory.cost = new_cost;

                if (MONAD_VM_UNLIKELY(memory.capacity < *new_size)) {
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

        template <Traits traits>
        [[gnu::always_inline]]
        void return_to(Context *parent)
        {
            if (parent != nullptr) {
                non_temporal_bzero(memory.data, memory.size);
                auto &p = parent->memory;
                MONAD_VM_DEBUG_ASSERT(memory.parent_handle == p.data_handle);
                if (MONAD_VM_UNLIKELY(
                        memory.data_handle != memory.parent_handle)) {
                    p.release();
                    p.data = memory.data - p.size;
                    p.capacity = memory.capacity + p.size;
                    p.data_handle = memory.data_handle;
                }
            }
            else {
                memory.clear();
            }
            // Clear the data_handle to prevent the memory destructor from
            // double freeing it:
            memory.data_handle = nullptr;
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

        template <Traits traits>
        evmc::Result copy_to_evmc_result();

    private:
        template <Traits traits>
        std::variant<std::span<std::uint8_t const>, evmc_status_code>
        copy_result_data();
    };

    // Update context.S accordingly if these offsets change:
    static_assert(offsetof(Context, gas_remaining) == 16);
    static_assert(offsetof(Context, memory) == 264);
    static_assert(offsetof(Memory, size) == 0);
    static_assert(offsetof(Memory, capacity) == 4);
    static_assert(offsetof(Memory, data) == 8);
    static_assert(offsetof(Memory, cost) == 16);
    static_assert(offsetof(Memory, data_handle) == 24);

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
    constexpr auto context_offset_env_tx_context =
        offsetof(Context, env) + offsetof(Environment, tx_context);
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
    monad::vm::runtime::Bin<30> new_size);

extern "C" void monad_vm_runtime_increase_memory_v1(
    monad::vm::runtime::Bin<29> min_size, monad::vm::runtime::Context *);
extern "C" void monad_vm_runtime_increase_memory_mip3(
    monad::vm::runtime::Bin<29> min_size, monad::vm::runtime::Context *);

// Note: monad_vm_runtime_increase_memory_raw_* uses non-standard
// calling convention. Context is passed in rbx and new min
// memory size if passed in rdi. See context.S. Use the
// monad_vm_runtime_increase_memory_* function for a version
// using standard calling convention
extern "C" void monad_vm_runtime_increase_memory_raw_v1();
extern "C" void monad_vm_runtime_increase_memory_raw_mip3();
