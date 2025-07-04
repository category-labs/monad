#pragma once

#include <monad/vm/core/assert.h>
#include <monad/vm/runtime/transmute.hpp>
#include <monad/vm/runtime/types.hpp>
#include <monad/vm/runtime/uint256.hpp>

#include <evmc/evmc.hpp>

#include <limits>

namespace monad::vm::runtime
{
    template <evmc_revision Rev>
    void
    balance(Context *ctx, uint256_t *result_ptr, uint256_t const *address_ptr)
    {
        auto address = address_from_uint256(*address_ptr);

        if constexpr (Rev >= EVMC_BERLIN) {
            auto access_status =
                ctx->host->access_account(ctx->context, &address);
            if (access_status == EVMC_ACCESS_COLD) {
                ctx->deduct_gas(2500);
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

    template <evmc_revision Rev>
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

        if constexpr (Rev >= EVMC_BERLIN) {
            auto access_status =
                ctx->host->access_account(ctx->context, &address);
            if (access_status == EVMC_ACCESS_COLD) {
                ctx->deduct_gas(2500);
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

    template <evmc_revision Rev>
    void extcodehash(
        Context *ctx, uint256_t *result_ptr, uint256_t const *address_ptr)
    {
        auto address = address_from_uint256(*address_ptr);

        if constexpr (Rev >= EVMC_BERLIN) {
            auto access_status =
                ctx->host->access_account(ctx->context, &address);
            if (access_status == EVMC_ACCESS_COLD) {
                ctx->deduct_gas(2500);
            }
        }

        auto hash = ctx->host->get_code_hash(ctx->context, &address);
        *result_ptr = uint256_from_bytes32(hash);
    }

    template <evmc_revision Rev>
    void extcodesize(
        Context *ctx, uint256_t *result_ptr, uint256_t const *address_ptr)
    {
        auto address = address_from_uint256(*address_ptr);

        if constexpr (Rev >= EVMC_BERLIN) {
            auto access_status =
                ctx->host->access_account(ctx->context, &address);
            if (access_status == EVMC_ACCESS_COLD) {
                ctx->deduct_gas(2500);
            }
        }

        *result_ptr = ctx->host->get_code_size(ctx->context, &address);
    }
}
