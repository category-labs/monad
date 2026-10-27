// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/byte_string.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <category/core/rlp/decode_error.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/monad/core/domain_block.hpp>
#include <category/execution/monad/core/rlp/domain_block_rlp.hpp>

#include <boost/outcome/try.hpp>

#include <cstdint>

MONAD_RLP_NAMESPACE_BEGIN

namespace
{
    Result<void> decode_empty_list(byte_string_view &enc)
    {
        BOOST_OUTCOME_TRY(auto const payload, parse_list_metadata(enc));
        if (MONAD_UNLIKELY(!payload.empty())) {
            return DecodeError::InputTooLong;
        }
        return outcome::success();
    }
}

byte_string encode_proposed_domain_header(ProposedDomainHeader const &header)
{
    byte_string encoded;
    encoded += encode_unsigned(header.domain_chain_id);
    encoded += encode_unsigned(header.number);
    encoded += encode_unsigned(header.l1_block_number);
    encoded += encode_bytes32(header.l1_block_id);
    encoded += encode_unsigned(header.timestamp);
    encoded += encode_bytes32(header.mix_hash);
    encoded += encode_unsigned(header.gas_limit);
    encoded += encode_unsigned(header.base_fee_per_gas);
    encoded += encode_bytes32(header.transactions_root);
    return encode_list2(encoded);
}

Result<ProposedDomainHeader>
decode_proposed_domain_header(byte_string_view &enc)
{
    ProposedDomainHeader header;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    BOOST_OUTCOME_TRY(
        header.domain_chain_id, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(header.number, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(
        header.l1_block_number, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(header.l1_block_id, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(header.timestamp, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(header.mix_hash, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(header.gas_limit, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(
        header.base_fee_per_gas, decode_unsigned<uint256_t>(payload));
    BOOST_OUTCOME_TRY(header.transactions_root, decode_bytes32(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }
    return header;
}

byte_string encode_domain_block(DomainBlock const &block)
{
    byte_string transactions;
    for (auto const &tx : block.transactions) {
        if (tx.type == TransactionType::legacy) {
            transactions += encode_transaction(tx);
        }
        else {
            transactions += encode_string2(encode_transaction(tx));
        }
    }

    byte_string body;
    body += encode_list2(transactions);
    body += encode_list2(byte_string{}); // ommers
    body += encode_list2(byte_string{}); // withdrawals

    byte_string encoded;
    encoded += encode_proposed_domain_header(block.header);
    encoded += encode_list2(body);
    return encode_list2(encoded);
}

Result<DomainBlock> decode_domain_block(byte_string_view &enc)
{
    DomainBlock block;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));
    BOOST_OUTCOME_TRY(block.header, decode_proposed_domain_header(payload));

    BOOST_OUTCOME_TRY(auto body, parse_list_metadata(payload));
    BOOST_OUTCOME_TRY(block.transactions, decode_transaction_list(body));
    BOOST_OUTCOME_TRY(decode_empty_list(body)); // ommers
    BOOST_OUTCOME_TRY(decode_empty_list(body)); // withdrawals

    if (MONAD_UNLIKELY(!body.empty() || !payload.empty())) {
        return DecodeError::InputTooLong;
    }
    return block;
}

MONAD_RLP_NAMESPACE_END
