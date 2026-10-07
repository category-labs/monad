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

#include <zkvm/guest/domain_body.hpp>

#include <category/core/likely.h>
#include <category/core/rlp/decode_error.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/ecrecover.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>

#include <boost/outcome/try.hpp>

#include <cstddef>
#include <cstdint>
#include <utility>

MONAD_NAMESPACE_BEGIN

Result<DomainBody> decode_domain_body(
    byte_string_view &enc, L2Cipher::Context const &ctx,
    L2Cipher::Secret const &secret, uint64_t const domain_chain_id,
    std::vector<byte_string_view> &ciphertexts, byte_string &plaintexts,
    std::vector<byte_string_view> &encodings)
{
    DomainBody body;
    BOOST_OUTCOME_TRY(auto payload, rlp::parse_list_metadata(enc));
    BOOST_OUTCOME_TRY(body.block.header, rlp::decode_block_header(payload));

    // The payloads and their envelopes' gas limits are two lists rather than a
    // list of pairs, so that the ciphertext list is exactly what the sequencing
    // anchor is taken over and needs no unwrapping to get there.
    BOOST_OUTCOME_TRY(auto items, rlp::parse_list_metadata(payload));
    while (!items.empty()) {
        BOOST_OUTCOME_TRY(auto const ct, rlp::parse_string_metadata(items));
        ciphertexts.push_back(ct);
    }

    std::vector<uint64_t> outer_gas_limits;
    outer_gas_limits.reserve(ciphertexts.size());
    {
        BOOST_OUTCOME_TRY(auto limits, rlp::parse_list_metadata(payload));
        while (!limits.empty()) {
            BOOST_OUTCOME_TRY(
                auto const limit, rlp::decode_unsigned<uint64_t>(limits));
            outer_gas_limits.push_back(limit);
        }
    }
    // One per payload. A body that disagrees with itself is malformed, not a
    // block whose extra entries are ignored.
    if (MONAD_UNLIKELY(outer_gas_limits.size() != ciphertexts.size())) {
        return rlp::DecodeError::ArrayLengthUnexpected;
    }

    BOOST_OUTCOME_TRY(
        body.parent_number, rlp::decode_unsigned<uint64_t>(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return rlp::DecodeError::InputTooLong;
    }

    // Reuse one plaintext buffer: decode_transaction copies calldata into
    // Transaction, so peak plaintext storage is the largest payload.
    std::vector<unsigned char> plain;
    // Where each accepted plaintext ends in `plaintexts`. Offsets and not
    // views, because the buffer may move while it grows.
    std::vector<std::size_t> ends;
    for (std::size_t i = 0; i < ciphertexts.size(); ++i) {
        if (!L2Cipher::decrypt(ctx, secret, ciphertexts[i], plain)) {
            continue; // dropped: consumed, nothing executed
        }
        byte_string_view leaf{plain.data(), plain.size()};
        auto tx = rlp::decode_transaction(leaf);
        // Exactly one transaction and nothing after it.
        if (MONAD_UNLIKELY(!tx.has_value() || !leaf.empty())) {
            continue; // dropped
        }
        // Drop transactions whose inner gas limit exceeds the L1 envelope's
        // sponsorship; execution cannot recover this outer-transaction fact.
        if (MONAD_UNLIKELY(tx.value().gas_limit > outer_gas_limits[i])) {
            continue; // dropped
        }
        // Drop missing or wrong signed chain ids, matching the client's
        // domain filter.
        if (MONAD_UNLIKELY(
                !tx.value().sc.chain_id.has_value() ||
                tx.value().sc.chain_id.value() != domain_chain_id)) {
            continue; // dropped
        }
        // Recover before execution so failures can be dropped; return senders
        // to avoid repeating recovery. Use the decoded signing bytes as
        // described in rlp::signing_payload.
        byte_string_view const encoding{plain.data(), plain.size()};
        auto const sender = recover_address(
            tx.value().sc.signature,
            rlp::signing_payload(tx.value(), encoding));
        if (MONAD_UNLIKELY(!sender.has_value())) {
            continue; // dropped
        }
        body.senders.push_back(*sender);
        body.block.transactions.emplace_back(std::move(tx).value());
        plaintexts.append(plain.data(), plain.size());
        ends.push_back(plaintexts.size());
    }
    encodings.reserve(ends.size());
    for (std::size_t begin = 0; std::size_t const end : ends) {
        encodings.emplace_back(plaintexts.data() + begin, end - begin);
        begin = end;
    }

    return body;
}

MONAD_NAMESPACE_END
