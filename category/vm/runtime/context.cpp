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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/cases.hpp>
#include <category/core/likely.h>
#include <category/core/runtime/non_temporal_memory.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/vm/evm/call_status.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/message.hpp>
#include <category/vm/evm/result.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/host.hpp>
#include <category/vm/runtime/bin.hpp>
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/types.hpp>

#if defined(MONAD_ZKVM_ZISK)
    #include <zkvm/core/arena.hpp>
#endif

#include <bit>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <span>
#include <type_traits>
#include <variant>

using namespace monad::vm::runtime;

// The x86 JIT calls monad_vm_runtime_increase_capacity with a 32-bit Bin
// argument. Preserve that ABI; the guest has no JIT and may use a wider Bin.
#ifdef MONAD_ZKVM_WIDE_MEMORY_SIZE
static_assert(sizeof(Bin<31>) == sizeof(Bin<31>::rep));
static_assert(alignof(Bin<31>) == alignof(Bin<31>::rep));
#else
static_assert(sizeof(Bin<31>) == sizeof(uint32_t));
static_assert(alignof(Bin<31>) == alignof(uint32_t));
#endif
static_assert(std::is_standard_layout_v<Bin<31>>);

extern "C" void monad_vm_runtime_increase_capacity(
    Context *const ctx, uint32_t const old_size, Bin<30> const new_size)
{
    MONAD_DEBUG_ASSERT((*new_size & 31) == 0);
    MONAD_DEBUG_ASSERT(old_size < *new_size);

    Bin<30> const parent_total_size = ctx->memory.parent_total_size();

    Bin<31> const old_total_size =
        parent_total_size + Bin<30>::unsafe_from(old_size);
    Bin<31> const new_total_size = parent_total_size + new_size;

    MONAD_DEBUG_ASSERT((*new_total_size & 31) == 0);

    Bin<32> const new_total_capacity = shl<1>(new_total_size);

    MONAD_DEBUG_ASSERT((*new_total_capacity & 31) == 0);

    auto *const new_handle =
        static_cast<uint8_t *>(std::aligned_alloc(32, *new_total_capacity));
    MONAD_ASSERT(new_handle);

    non_temporal_memcpy(new_handle, ctx->memory.data_handle, *old_total_size);
    non_temporal_bzero(
        new_handle + *old_total_size, *new_total_capacity - *old_total_size);

    ctx->memory.release();
    ctx->memory.capacity = *new_total_capacity - *parent_total_size;
    ctx->memory.data_handle = new_handle;
    ctx->memory.data = new_handle + *parent_total_size;
}

namespace monad::vm::runtime
{
    Context Context::from(
        Host &host, Message const *const msg,
        std::span<uint8_t const> const code) noexcept
    {
        return Context{
            .host = &host,
            .gas_remaining = msg->gas,
            .gas_refund = 0,
            .env =
                {
                    .flags = msg->flags,
                    .depth = msg->depth,
                    .recipient = msg->recipient,
                    .sender = msg->sender,
                    .value = static_cast<bytes32_t>(msg->value),
#if defined(MONAD_ZKVM_ZISK)
        // Only CREATE2 reads the salt directly from its message.
#else
                    .create2_salt = static_cast<bytes32_t>(msg->create2_salt),
#endif
                    .input_data = msg->input_data,
                    .code = code.data(),
                    .return_data = {},
                    .input_data_size = static_cast<env_size_t>(msg->input_size),
                    .code_size = static_cast<env_size_t>(code.size()),
                    .return_data_size = 0,
#if defined(MONAD_ZKVM_ZISK)
                    .tx_context = guest_get_tx_context(host),
#else
                    .tx_context = host.get_tx_context(),
#endif
                },
            .result = {},
            .memory =
                Memory(msg->memory_handle, msg->memory, msg->memory_capacity),
        };
    }

    Context Context::empty(
        uint8_t *const memory_handle, uint32_t const memory_capacity) noexcept
    {
        return Context{
            .host = nullptr,
            .gas_remaining = 0,
            .gas_refund = 0,
            .env =
                {
                    .flags = 0,
                    .depth = 0,
                    .recipient = Address{},
                    .sender = Address{},
                    .value = bytes32_t{},
                    .create2_salt = bytes32_t{},
                    .input_data = nullptr,
                    .code = {},
                    .return_data = {},
                    .input_data_size = 0,
                    .code_size = 0,
                    .return_data_size = 0,
                    .tx_context = {},
                },
            .result = {},
            .memory = Memory(memory_handle, memory_handle, memory_capacity),
        };
    }

    void
    Context::increase_capacity(uint32_t const old_size, Bin<30> const new_size)
    {
        monad_vm_runtime_increase_capacity(this, old_size, new_size);
    }

    template <Traits traits>
    std::variant<std::span<uint8_t const>, CallStatus>
    Context::copy_result_data()
    {
        if (gas_remaining < 0) {
            return CallStatus::OutOfGas;
        }

#if defined(MONAD_ZKVM_ZISK)
        // Read the 64-bit limbs directly to avoid staging a 32-byte copy on the
        // stack.
        auto const load_limb = [](uint8_t const *const bytes,
                                  unsigned const index) {
            uint64_t limb;
            __builtin_memcpy(&limb, bytes + sizeof(limb) * index, sizeof(limb));
            return limb;
        };
        auto const fits_memory_offset = [&](uint8_t const *const bytes) {
            return ((load_limb(bytes, 0) >> Memory::offset_bits) |
                    load_limb(bytes, 1) | load_limb(bytes, 2) |
                    load_limb(bytes, 3)) == 0;
        };
        if (!fits_memory_offset(result.size)) {
            return CallStatus::OutOfGas;
        }

        auto const size = Memory::Offset::unsafe_from(
            static_cast<Memory::Offset::rep>(load_limb(result.size, 0)));
        if (*size == 0) {
            return std::span<uint8_t const>({});
        }

        if (!fits_memory_offset(result.offset)) {
            return CallStatus::OutOfGas;
        }

        auto const offset = Memory::Offset::unsafe_from(
            static_cast<Memory::Offset::rep>(load_limb(result.offset, 0)));
#else
        auto const size_word = std::bit_cast<uint256_t>(result.size);
        if (!is_bounded_by_bits<Memory::offset_bits>(size_word)) {
            return CallStatus::OutOfGas;
        }

        auto const size =
            Memory::Offset::unsafe_from(static_cast<uint32_t>(size_word));
        if (*size == 0) {
            return std::span<uint8_t const>({});
        }

        auto const offset_word = std::bit_cast<uint256_t>(result.offset);
        if (!is_bounded_by_bits<Memory::offset_bits>(offset_word)) {
            return CallStatus::OutOfGas;
        }

        auto const offset =
            Memory::Offset::unsafe_from(static_cast<uint32_t>(offset_word));
#endif

        auto const memory_end = offset + size;

        // We want to avoid preallocating the output buffer: if we run out of
        // gas, then we need to immediately free the buffer if it was allocated
        // ahead of time, which is inefficient. To keep the gas check in-line as
        // a single subtraction and comparison with zero, we use this lambda to
        // deduplicate the two cases in which we need to allocate an output
        // buffer (when the memory is already big enough, and when we've paid
        // the cost of a necessary expansion).
        uint8_t *output_buf = nullptr;
        auto allocate_output_buf = [size] {
#if defined(MONAD_ZKVM_ZISK)
            // Use the inline arena fast path to avoid a malloc call.
            // Result's free is a no-op in this guest.
            return static_cast<uint8_t *>(zkvm_arena_alloc(*size));
#else
            return reinterpret_cast<uint8_t *>(std::malloc(*size));
#endif
        };

        if (*memory_end <= memory.size) {
            output_buf = allocate_output_buf();
            std::memcpy(output_buf, memory.data + *offset, *size);
        }
        else {
            if (MONAD_UNLIKELY(!is_memory_size_in_bound<traits>(memory_end))) {
                // Return out-of-gas error code, similar to when an
                // `is_bounded_by_bits` check fails.
                return CallStatus::OutOfGas;
            }

            auto const memory_cost =
                Context::memory_cost_from_word_count<traits>(
                    Context::memory_size_to_word_count(memory_end));
            gas_remaining -= memory_cost - memory.cost;

            if (gas_remaining < 0) {
                return CallStatus::OutOfGas;
            }

            output_buf = allocate_output_buf();

            if (*offset < memory.size) {
                auto const n = memory.size - *offset;
                std::memcpy(output_buf, memory.data + *offset, n);
                std::memset(output_buf + n, 0, *memory_end - memory.size);
            }
            else {
                std::memset(output_buf, 0, *size);
            }
        }

        return std::span{output_buf, *size};
    }

    EXPLICIT_TRAITS_MEMBER(Context::copy_result_data);

    template <Traits traits>
    vm::Result Context::copy_to_result()
    {
        using enum StatusCode;

        if (MONAD_UNLIKELY(result.status == Error)) {
            return vm::Result{CallStatus::Failure};
        }
        if (MONAD_UNLIKELY(result.status == OutOfGas)) {
            return vm::Result{CallStatus::OutOfGas};
        }

        MONAD_DEBUG_ASSERT(result.status == Success || result.status == Revert);

        return std::visit(
            Cases{
                [](CallStatus ec) { return vm::Result{ec}; },
                [this](std::span<uint8_t const> output) {
#if defined(MONAD_ZKVM_ZISK)
                    // Attach the buffer already allocated by copy_result_data.
                    vm::Result call_result{
                        result.status == Success ? CallStatus::Success
                                                 : CallStatus::Revert,
                        gas_remaining,
                        result.status == Success ? gas_refund : 0};
                    call_result.output_data = output.data();
                    call_result.output_size = output.size();
                    return call_result;
#else
                    return vm::Result{vm::RawResult{
                        .status_code = result.status == Success
                                           ? CallStatus::Success
                                           : CallStatus::Revert,
                        .gas_left = gas_remaining,
                        .gas_refund = result.status == Success ? gas_refund : 0,
                        .output_data = output.data(),
                        .output_size = output.size(),
                        .create_address = {},
                    }};
#endif
                }},
            copy_result_data<traits>());
    }

    EXPLICIT_TRAITS_MEMBER(Context::copy_to_result);
}
