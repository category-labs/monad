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
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/types.hpp>

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

        auto const block_number = static_cast<std::int64_t>(*block_number_ptr);
        auto const &tx_context = *ctx->env.tx_context;

        auto const first_allowed_block =
            std::max(tx_context.block_number - 256, 0L);
        if (block_number >= first_allowed_block &&
            block_number < tx_context.block_number) {
            auto const hash =
                ctx->host->get_block_hash(ctx->context, block_number);
            *result_ptr = uint256_from_bytes32(hash);
        }
        else {
            *result_ptr = 0;
        }
    }

    inline void selfbalance(Context *ctx, uint256_t *result_ptr)
    {
        auto const balance =
            ctx->host->get_balance(ctx->context, &ctx->env.recipient);
        *result_ptr = uint256_from_bytes32(balance);
    }

    inline void
    blobhash(Context *ctx, uint256_t *result_ptr, uint256_t const *index)
    {
        auto const &c = *ctx->env.tx_context;
        *result_ptr = (*index < c.blob_hashes_count)
                          ? uint256_from_bytes32(
                                c.blob_hashes[static_cast<size_t>(*index)])
                          : 0;
    }
}
