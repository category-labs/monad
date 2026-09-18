// Copyright (C) 2026 Category Labs, Inc.
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

// See decode_block_l2.hpp for the wire shape and the rejection rule.

#include <zkvm/guest/decode_block_l2.hpp>

#include <category/core/likely.h>
#include <category/core/rlp/decode_error.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/rlp/withdrawal_rlp.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>

#include <boost/outcome/try.hpp>

#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

Result<Block> decode_block_l2(
    byte_string_view &enc, L2Cipher::Context const &ctx,
    L2Cipher::Secret const &secret, std::vector<byte_string_view> &ciphertexts)
{
    Block block;
    BOOST_OUTCOME_TRY(auto payload, rlp::parse_list_metadata(enc));
    BOOST_OUTCOME_TRY(block.header, rlp::decode_block_header(payload));

    BOOST_OUTCOME_TRY(auto items, rlp::parse_list_metadata(payload));
    // One buffer for the block, reused per leaf: Transaction owns its calldata
    // -- decode_string copies into it -- so a plaintext's life ends when
    // decode_transaction returns, and the peak is the largest transaction
    // rather than the block.
    std::vector<unsigned char> plain;
    while (!items.empty()) {
        BOOST_OUTCOME_TRY(auto const ct, rlp::parse_string_metadata(items));
        ciphertexts.push_back(ct);

        if (!L2Cipher::decrypt(ctx, secret, ct, plain)) {
            continue; // rejected: consumed, nothing executed
        }
        byte_string_view leaf{plain.data(), plain.size()};
        auto tx = rlp::decode_transaction(leaf);
        // Exactly one transaction and nothing after it.
        if (MONAD_UNLIKELY(!tx.has_value() || !leaf.empty())) {
            continue; // rejected
        }
        block.transactions.emplace_back(std::move(tx).value());
    }

    BOOST_OUTCOME_TRY(block.ommers, rlp::decode_block_header_vector(payload));

    if (payload.size() > 0) {
        BOOST_OUTCOME_TRY(
            auto withdrawals, rlp::decode_withdrawal_list(payload));
        block.withdrawals.emplace(std::move(withdrawals));
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return rlp::DecodeError::InputTooLong;
    }

    return block;
}

MONAD_NAMESPACE_END
