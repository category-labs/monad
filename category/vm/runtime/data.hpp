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
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/runtime/uint256.hpp>

#include <evmc/evmc.hpp>

#include <limits>

namespace monad::vm::runtime
{
    template <Traits traits>
    void
    balance(Context *ctx, uint256_t *result_ptr, uint256_t const *address_ptr)
    {
        auto address = address_from_uint256(*address_ptr);

        if constexpr (traits::eip_2929_active()) {
            auto access_status =
                ctx->host->access_account(ctx->context, &address);
            if (access_status == EVMC_ACCESS_COLD) {
                ctx->deduct_gas(traits::cold_account_cost());
            }
        }

        auto balance = ctx->host->get_balance(ctx->context, &address);
        *result_ptr = uint256_from_bytes32(balance);
    }

    inline void
    calldataload(Context *ctx, uint256_t *result_ptr, uint256_t const *i_ptr)
    {
        if (MONAD_VM_UNLIKELY(!is_bounded_by_bits<32>(*i_ptr))) {
            *result_ptr = 0;
            return;
        }

        auto const i{static_cast<std::uint32_t>(*i_ptr)};
        auto const n = int64_t{ctx->env.input_data_size} - int64_t{i};
        if (MONAD_VM_UNLIKELY(n <= 0)) {
            // Prevent undefined behavior from pointer arithmetic out of bounds.
            *result_ptr = 0;
            return;
        }

        *result_ptr = uint256_load_bounded_be(ctx->env.input_data + i, n);
    }

    inline void copy_impl(
        Context *ctx, uint256_t const &dest_offset_word,
        uint256_t const &offset_word, uint256_t const &size_word,
        std::uint8_t const *source, std::uint32_t len)
    {
        auto size = ctx->get_memory_offset(size_word);
        if (*size == 0) {
            return;
        }

        auto dest_offset = ctx->get_memory_offset(dest_offset_word);

        ctx->expand_memory(dest_offset + size);

        auto size_in_words = shr_ceil<5>(size);
        ctx->deduct_gas(size_in_words * bin<3>);

        std::uint32_t const start =
            is_bounded_by_bits<32>(offset_word)
                ? std::min(static_cast<std::uint32_t>(offset_word), len)
                : len;

        auto copy_size = std::min(*size, len - start);
        auto *dest_ptr = ctx->memory.data + *dest_offset;
        std::copy_n(source + start, copy_size, dest_ptr);
        std::fill_n(dest_ptr + copy_size, *size - copy_size, 0);
    }

    inline void calldatacopy(
        Context *ctx, uint256_t const *dest_offset_ptr,
        uint256_t const *offset_ptr, uint256_t const *size_ptr)
    {
        copy_impl(
            ctx,
            *dest_offset_ptr,
            *offset_ptr,
            *size_ptr,
            ctx->env.input_data,
            ctx->env.input_data_size);
    }

    inline void codecopy(
        Context *ctx, uint256_t const *dest_offset_ptr,
        uint256_t const *offset_ptr, uint256_t const *size_ptr)
    {
        copy_impl(
            ctx,
            *dest_offset_ptr,
            *offset_ptr,
            *size_ptr,
            ctx->env.code,
            ctx->env.code_size);
    }

    template <Traits traits>
    void extcodecopy(
        Context *ctx, uint256_t const *address_ptr,
        uint256_t const *dest_offset_ptr, uint256_t const *offset_ptr,
        uint256_t const *size_ptr)
    {
        auto size = ctx->get_memory_offset(*size_ptr);
        Memory::Offset dest_offset;

        if (*size > 0) {
            dest_offset = ctx->get_memory_offset(*dest_offset_ptr);

            ctx->expand_memory(dest_offset + size);

            auto size_in_words = shr_ceil<5>(size);
            ctx->deduct_gas(size_in_words * bin<3>);
        }

        auto address = address_from_uint256(*address_ptr);

        if constexpr (traits::eip_2929_active()) {
            auto access_status =
                ctx->host->access_account(ctx->context, &address);
            if (access_status == EVMC_ACCESS_COLD) {
                ctx->deduct_gas(traits::cold_account_cost());
            }
        }

        if (*size > 0) {
            auto offset = clamp_cast<std::uint32_t>(*offset_ptr);

            auto *dest_ptr = ctx->memory.data + *dest_offset;
            auto n = ctx->host->copy_code(
                ctx->context, &address, offset, dest_ptr, *size);

            auto *begin = dest_ptr + static_cast<std::uint32_t>(n);
            auto *end = dest_ptr + *size;

            std::fill(begin, end, 0);
        }
    }

    inline void returndatacopy(
        Context *ctx, uint256_t const *dest_offset_ptr,
        uint256_t const *offset_ptr, uint256_t const *size_ptr)
    {
        auto size = ctx->get_memory_offset(*size_ptr);
        auto offset = clamp_cast<std::uint32_t>(*offset_ptr);

        std::uint32_t end;
        if (MONAD_VM_UNLIKELY(
                __builtin_add_overflow(offset, *size, &end) ||
                end > ctx->env.return_data_size)) {
            ctx->exit(StatusCode::OutOfGas);
        }

        if (*size > 0) {
            auto dest_offset = ctx->get_memory_offset(*dest_offset_ptr);

            ctx->expand_memory(dest_offset + size);

            auto size_in_words = shr_ceil<5>(size);
            ctx->deduct_gas(size_in_words * bin<3>);

            std::copy_n(
                ctx->env.return_data + offset,
                *size,
                ctx->memory.data + *dest_offset);
        }
    }

    template <Traits traits>
    void extcodehash(
        Context *ctx, uint256_t *result_ptr, uint256_t const *address_ptr)
    {
        auto address = address_from_uint256(*address_ptr);

        if constexpr (traits::eip_2929_active()) {
            auto access_status =
                ctx->host->access_account(ctx->context, &address);
            if (access_status == EVMC_ACCESS_COLD) {
                ctx->deduct_gas(traits::cold_account_cost());
            }
        }

        auto hash = ctx->host->get_code_hash(ctx->context, &address);
        *result_ptr = uint256_from_bytes32(hash);
    }

    template <Traits traits>
    void extcodesize(
        Context *ctx, uint256_t *result_ptr, uint256_t const *address_ptr)
    {
        auto address = address_from_uint256(*address_ptr);

        if constexpr (traits::eip_2929_active()) {
            auto access_status =
                ctx->host->access_account(ctx->context, &address);
            if (access_status == EVMC_ACCESS_COLD) {
                ctx->deduct_gas(traits::cold_account_cost());
            }
        }

        *result_ptr = ctx->host->get_code_size(ctx->context, &address);
    }
}
