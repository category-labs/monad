#pragma once

#include <monad/vm/runtime/transmute.hpp>
#include <monad/vm/runtime/types.hpp>
#include <monad/vm/runtime/uint256.hpp>

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

    template <evmc_revision Rev>
    uint256_t create_impl(
        Context *ctx, uint256_t const &value, uint256_t const &offset_word,
        uint256_t const &size_word, uint256_t const &salt_word,
        evmc_call_kind kind, std::int64_t remaining_block_base_gas)
    {
        if (MONAD_VM_UNLIKELY(ctx->env.evmc_flags & EVMC_STATIC)) {
            ctx->exit(StatusCode::Error);
        }

        ctx->env.clear_return_data();

        Memory::Offset offset;
        auto size = ctx->get_memory_offset(size_word);

        if (*size > 0) {
            offset = ctx->get_memory_offset(offset_word);
            ctx->expand_memory(offset + size);
        }

        if constexpr (Rev >= EVMC_SHANGHAI) {
            if (MONAD_VM_UNLIKELY(*size > 0xC000)) {
                ctx->exit(StatusCode::OutOfGas);
            }
        }

        auto min_words = shr_ceil<5>(size);
        auto word_cost = (kind == EVMC_CREATE2) ? create2_code_word_cost(Rev)
                                                : create_code_word_cost(Rev);

        ctx->deduct_gas(min_words * word_cost);

        if (MONAD_VM_UNLIKELY(ctx->env.depth >= 1024)) {
            return 0;
        }

        auto gas = ctx->gas_remaining + remaining_block_base_gas;
        if constexpr (Rev >= EVMC_TANGERINE_WHISTLE) {
            gas = gas - (gas / 64);
        }

        auto message = evmc_message{
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
            .code = nullptr,
            .code_size = 0,
        };

        auto result = ctx->host->call(ctx->context, &message);

        ctx->deduct_gas(gas - result.gas_left);
        ctx->gas_refund += result.gas_refund;
        ctx->env.set_return_data(result.output_data, result.output_size);

        return (result.status_code == EVMC_SUCCESS)
                   ? uint256_from_address(result.create_address)
                   : 0;
    }

    template <evmc_revision Rev>
    void create(
        Context *ctx, uint256_t *result_ptr, uint256_t const *value_ptr,
        uint256_t const *offset_ptr, uint256_t const *size_ptr,
        std::int64_t remaining_block_base_gas)
    {
        *result_ptr = create_impl<Rev>(
            ctx,
            *value_ptr,
            *offset_ptr,
            *size_ptr,
            0,
            EVMC_CREATE,
            remaining_block_base_gas);
    }

    template <evmc_revision Rev>
    void create2(
        Context *ctx, uint256_t *result_ptr, uint256_t const *value_ptr,
        uint256_t const *offset_ptr, uint256_t const *size_ptr,
        uint256_t const *salt_ptr, std::int64_t remaining_block_base_gas)
    {
        *result_ptr = create_impl<Rev>(
            ctx,
            *value_ptr,
            *offset_ptr,
            *size_ptr,
            *salt_ptr,
            EVMC_CREATE2,
            remaining_block_base_gas);
    }
}
