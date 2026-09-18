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
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_block.hpp>

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

    // EIP-7685's requests are protocol-initiated execution for a beacon chain
    // this one does not have: no validators, no deposits, no exits. The
    // epilogue therefore computes no requests hash, so a header claiming one
    // would carry a value nothing checks. Rejected rather than ignored.
    // Rejected on PRESENCE, not on content: the epilogue computes no requests
    // hash, so any value here is one nothing checks. A Prague-or-later header
    // carries keccak256("") even with no requests, which is why the corpus
    // differential needs l2_allows_l1_shape to get past this at all.
    if constexpr (!l2_allows_l1_shape()) {
        if (MONAD_UNLIKELY(block.header.requests_hash.has_value())) {
            return BlockError::RequestsNotSupported;
        }
    }

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
    // Ommers have no meaning on this chain, and leaving them accepted would
    // leave apply_block_reward's ommer credits reachable -- they are zero on
    // Paris and later, which the revision's static_assert pins, but this is the
    // list itself rather than one more thing depending on that assert.
    if (MONAD_UNLIKELY(!block.ommers.empty())) {
        return BlockError::OmmersNotSupported;
    }

    if (payload.size() > 0) {
        BOOST_OUTCOME_TRY(
            auto withdrawals, rlp::decode_withdrawal_list(payload));
        // A withdrawal credits its recipient directly, and on this chain
        // nothing authenticates the list. The block RLP is the prover's, the
        // withdrawals root is checked only against the prover's own header,
        // and the block hash this run publishes is computed from that same
        // header -- so there is no external fact any of it is pinned to. An
        // entry here would be balance created from nothing, provable.
        //
        // An empty list is allowed so a Shanghai-or-later header can still
        // carry a well-formed withdrawals root. A real L2 needs an
        // authenticated deposit path and this is where it would attach: the
        // list would have to be bound to deposits the L1 hub has accepted,
        // not merely to a header the prover wrote.
        // l2_allows_l1_shape lifts this for the corpus differential, and
        // lifting the rejection is all it does: the epilogue still does not
        // credit them, so even that build creates no balance.
        if constexpr (!l2_allows_l1_shape()) {
            if (MONAD_UNLIKELY(!withdrawals.empty())) {
                return BlockError::WithdrawalsNotSupported;
            }
        }
        block.withdrawals.emplace(std::move(withdrawals));
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return rlp::DecodeError::InputTooLong;
    }

    return block;
}

MONAD_NAMESPACE_END
