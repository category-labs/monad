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

#include <category/core/runtime/uint256.hpp>
#include <category/vm/evm/delegation.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.hpp>

namespace monad::vm::runtime
{
    consteval Bin<2> create_code_word_cost(evmc_revision rev)
    {
        return (rev >= EVMC_SHANGHAI) ? bin<2> : bin<0>;
    }

    consteval Bin<4> create2_code_word_cost(evmc_revision rev)
    {
        return (rev >= EVMC_SHANGHAI) ? bin<8> : bin<6>;
    }

    template <Traits traits>
    uint256_t create_impl(
        Context *ctx, uint256_t const &value, uint256_t const &offset_word,
        uint256_t const &size_word, uint256_t const &salt_word,
        evmc_call_kind kind, std::int64_t remaining_block_base_gas)
    {
        if (MONAD_VM_UNLIKELY(ctx->env.evmc_flags & EVMC_STATIC)) {
            ctx->exit(StatusCode::Error);
        }

        if constexpr (
            traits::evm_rev() >= EVMC_PRAGUE &&
            !traits::can_create_inside_delegated()) {
            if (evm::resolve_delegation(
                    ctx->host, ctx->context, ctx->env.recipient)) {
                ctx->exit(StatusCode::Error);
            }
        }

        ctx->env.clear_return_data();

        Memory::Offset offset;
        auto const size = ctx->get_memory_offset(size_word);

        if (*size > 0) {
            offset = ctx->get_memory_offset(offset_word);
            ctx->expand_memory<traits>(offset + size);
        }

        if constexpr (traits::evm_rev() >= EVMC_SHANGHAI) {
            if (MONAD_VM_UNLIKELY(*size > traits::max_initcode_size())) {
                ctx->exit(StatusCode::OutOfGas);
            }
        }

        auto const min_words = shr_ceil<5>(size);
        auto const word_cost = (kind == EVMC_CREATE2)
                                   ? create2_code_word_cost(traits::evm_rev())
                                   : create_code_word_cost(traits::evm_rev());

        ctx->deduct_gas(min_words * word_cost);

        if (MONAD_VM_UNLIKELY(ctx->env.depth >= 1024)) {
            return 0;
        }

        auto gas = ctx->gas_remaining + remaining_block_base_gas;
        gas = gas - (gas / 64);

        auto const message = evmc_message{
            .kind = kind,
            .flags = 0,
            .depth = ctx->env.depth + 1,
            .gas = gas,
            .recipient = evmc::address{},
            .sender = ctx->env.recipient,
            .input_data = (*size > 0) ? ctx->memory.data + *offset : nullptr,
            .input_size = *size,
            .value = bytes32_from_uint256(value),
            .create2_salt = bytes32_from_uint256(salt_word),
            .code_address = evmc::address{},
            .memory_handle = ctx->memory.data_handle,
            .memory = ctx->memory.data + ctx->memory.size,
            .memory_capacity = ctx->memory.capacity - ctx->memory.size,
        };

        auto const result = ctx->host->call(ctx->context, &message);

        ctx->env.set_return_data(result.output_data, result.output_size);

        // Unwind the stack after setting return data, so that return data
        // is deallocated by the `Environment` destructor.
        ctx->propagate_stack_unwind();

        ctx->deduct_gas(gas - result.gas_left);
        ctx->gas_refund += result.gas_refund;

        return (result.status_code == EVMC_SUCCESS)
                   ? uint256_from_address(result.create_address)
                   : 0;
    }

    template <Traits traits>
    void create(
        Context *ctx, uint256_t *result_ptr, uint256_t const *value_ptr,
        uint256_t const *offset_ptr, uint256_t const *size_ptr,
        std::int64_t remaining_block_base_gas)
    {
        *result_ptr = create_impl<traits>(
            ctx,
            *value_ptr,
            *offset_ptr,
            *size_ptr,
            0,
            EVMC_CREATE,
            remaining_block_base_gas);
    }

    template <Traits traits>
    void create2(
        Context *ctx, uint256_t *result_ptr, uint256_t const *value_ptr,
        uint256_t const *offset_ptr, uint256_t const *size_ptr,
        uint256_t const *salt_ptr, std::int64_t remaining_block_base_gas)
    {
        *result_ptr = create_impl<traits>(
            ctx,
            *value_ptr,
            *offset_ptr,
            *size_ptr,
            *salt_ptr,
            EVMC_CREATE2,
            remaining_block_base_gas);
    }
}
