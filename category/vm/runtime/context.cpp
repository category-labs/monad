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

#include <category/core/runtime/non_temporal_memory.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/core/cases.hpp>
#include <category/vm/runtime/bin.hpp>
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <bit>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <span>
#include <type_traits>
#include <variant>

using namespace monad::vm::runtime;

static_assert(sizeof(Bin<31>) == sizeof(uint32_t));
static_assert(alignof(Bin<31>) == alignof(uint32_t));
static_assert(std::is_standard_layout_v<Bin<31>>);

extern "C" void monad_vm_runtime_increase_capacity(
    Context *ctx, uint32_t old_size, Bin<30> new_size)
{
    MONAD_VM_DEBUG_ASSERT((*new_size & 31) == 0);
    MONAD_VM_DEBUG_ASSERT(old_size < *new_size);

    Bin<30> const parent_total_size = ctx->memory.parent_total_size();

    Bin<31> const old_total_size =
        parent_total_size + Bin<30>::unsafe_from(old_size);
    Bin<31> const new_total_size = parent_total_size + new_size;

    MONAD_VM_DEBUG_ASSERT((*new_total_size & 31) == 0);

    Bin<32> const new_total_capacity = shl<1>(new_total_size);

    MONAD_VM_DEBUG_ASSERT((*new_total_capacity & 31) == 0);

    auto *const new_handle =
        static_cast<uint8_t *>(std::aligned_alloc(32, *new_total_capacity));
    MONAD_VM_ASSERT(new_handle);

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
    namespace
    {
        void release_result(evmc_result const *result)
        {
            MONAD_VM_DEBUG_ASSERT(result);
            std::free(const_cast<std::uint8_t *>(result->output_data));
        }
    }

    Context Context::from(
        evmc_host_interface const *host, evmc_host_context *context,
        evmc_message const *msg, std::span<std::uint8_t const> code) noexcept
    {
        return Context{
            .host = host,
            .context = context,
            .gas_remaining = msg->gas,
            .gas_refund = 0,
            .env =
                {
                    .evmc_flags = msg->flags,
                    .depth = msg->depth,
                    .recipient = msg->recipient,
                    .sender = msg->sender,
                    .value = msg->value,
                    .create2_salt = msg->create2_salt,
                    .input_data = msg->input_data,
                    .code = code.data(),
                    .return_data = {},
                    .input_data_size =
                        static_cast<std::uint32_t>(msg->input_size),
                    .code_size = static_cast<std::uint32_t>(code.size()),
                    .return_data_size = 0,
                    .tx_context = host->get_tx_context(context),
                },
            .result = {},
            .memory =
                Memory(msg->memory_handle, msg->memory, msg->memory_capacity),
        };
    }

    Context Context::empty(
        std::uint8_t *const memory_handle,
        std::uint32_t memory_capacity) noexcept
    {
        return Context{
            .host = nullptr,
            .context = nullptr,
            .gas_remaining = 0,
            .gas_refund = 0,
            .env =
                {
                    .evmc_flags = 0,
                    .depth = 0,
                    .recipient = evmc::address{},
                    .sender = evmc::address{},
                    .value = evmc::bytes32{},
                    .create2_salt = evmc::bytes32{},
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

    void Context::increase_capacity(uint32_t old_size, Bin<30> new_size)
    {
        monad_vm_runtime_increase_capacity(this, old_size, new_size);
    }

    static evmc::Result evmc_error_result(evmc_status_code const code) noexcept
    {
        return evmc::Result{evmc_result{
            .status_code = code,
            .gas_left = 0,
            .gas_refund = 0,
            .output_data = nullptr,
            .output_size = 0,
            .release = nullptr,
            .create_address = {},
            .padding = {},
        }};
    }

    std::variant<std::span<std::uint8_t const>, evmc_status_code>
    Context::copy_result_data()
    {
        if (gas_remaining < 0) {
            return EVMC_OUT_OF_GAS;
        }

        auto const size_word = std::bit_cast<uint256_t>(result.size);
        if (!is_bounded_by_bits<Memory::offset_bits>(size_word)) {
            return EVMC_OUT_OF_GAS;
        }

        auto const size =
            Memory::Offset::unsafe_from(static_cast<uint32_t>(size_word));
        if (*size == 0) {
            return std::span<std::uint8_t const>({});
        }

        auto const offset_word = std::bit_cast<uint256_t>(result.offset);
        if (!is_bounded_by_bits<Memory::offset_bits>(offset_word)) {
            return EVMC_OUT_OF_GAS;
        }

        auto const offset =
            Memory::Offset::unsafe_from(static_cast<uint32_t>(offset_word));

        auto const memory_end = offset + size;

        // We want to avoid preallocating the output buffer: if we run out of
        // gas, then we need to immediately free the buffer if it was allocated
        // ahead of time, which is inefficient. To keep the gas check in-line as
        // a single subtraction and comparison with zero, we use this lambda to
        // deduplicate the two cases in which we need to allocate an output
        // buffer (when the memory is already big enough, and when we've paid
        // the cost of a necessary expansion).
        std::uint8_t *output_buf = nullptr;
        auto allocate_output_buf = [size] {
            return reinterpret_cast<std::uint8_t *>(std::malloc(*size));
        };

        if (*memory_end <= memory.size) {
            output_buf = allocate_output_buf();
            std::memcpy(output_buf, memory.data + *offset, *size);
        }
        else {
            auto const memory_cost =
                Context::memory_cost_from_word_count(shr_ceil<5>(memory_end));
            gas_remaining -= memory_cost - memory.cost;

            if (gas_remaining < 0) {
                return EVMC_OUT_OF_GAS;
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

    evmc::Result Context::copy_to_evmc_result()
    {
        using enum StatusCode;

        if (MONAD_VM_UNLIKELY(result.status == Error)) {
            return evmc_error_result(EVMC_FAILURE);
        }
        if (MONAD_VM_UNLIKELY(result.status == OutOfGas)) {
            return evmc_error_result(EVMC_OUT_OF_GAS);
        }

        MONAD_VM_DEBUG_ASSERT(
            result.status == Success || result.status == Revert);

        return std::visit(
            Cases{
                [](evmc_status_code ec) { return evmc_error_result(ec); },
                [this](std::span<std::uint8_t const> output) {
                    return evmc::Result{evmc_result{
                        .status_code = result.status == Success ? EVMC_SUCCESS
                                                                : EVMC_REVERT,
                        .gas_left = gas_remaining,
                        .gas_refund = result.status == Success ? gas_refund : 0,
                        .output_data = output.data(),
                        .output_size = output.size(),
                        .release = release_result,
                        .create_address = {},
                        .padding = {},
                    }};
                }},
            copy_result_data());
    }
}
