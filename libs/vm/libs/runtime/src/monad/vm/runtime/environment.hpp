#pragma once

#include <monad/vm/runtime/transmute.hpp>
#include <monad/vm/runtime/types.hpp>
#include <monad/vm/runtime/uint256.hpp>

#include <evmc/evmc.hpp>

#include <limits>

namespace monad::vm::runtime
{
    inline void blockhash(
        Context *ctx, uint256_t *result_ptr, uint256_t const *block_number_ptr)
    {
        if (!is_bounded_by_bits<63>(*block_number_ptr)) {
            *result_ptr = 0;
            return;
        }

        auto block_number = static_cast<std::int64_t>(*block_number_ptr);
        auto const &tx_context = ctx->env.tx_context;

        auto first_allowed_block = std::max(tx_context.block_number - 256, 0L);
        if (block_number >= first_allowed_block &&
            block_number < tx_context.block_number) {
            auto hash = ctx->host->get_block_hash(ctx->context, block_number);
            *result_ptr = uint256_from_bytes32(hash);
        }
        else {
            *result_ptr = 0;
        }
    }

    inline void selfbalance(Context *ctx, uint256_t *result_ptr)
    {
        auto balance =
            ctx->host->get_balance(ctx->context, &ctx->env.recipient);
        *result_ptr = uint256_from_bytes32(balance);
    }

    inline void
    blobhash(Context *ctx, uint256_t *result_ptr, uint256_t const *index)
    {
        auto const &c = ctx->env.tx_context;
        *result_ptr = (*index < c.blob_hashes_count)
                          ? uint256_from_bytes32(
                                c.blob_hashes[static_cast<size_t>(*index)])
                          : 0;
    }
}
