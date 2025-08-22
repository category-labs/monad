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

#include <category/execution/ethereum/core/rlp/address_rlp.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/rlp/withdrawal_rlp.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/decode_error.hpp>
#include <category/execution/monad/core/rlp/monad_block_rlp.hpp>

#include <vector>

MONAD_RLP_ANONYMOUS_NAMESPACE_BEGIN

Result<BlockHeader> decode_execution_inputs(byte_string_view &enc)
{
    BlockHeader header;

    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));
    BOOST_OUTCOME_TRY(header.ommers_hash, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(header.beneficiary, decode_address(payload));
    BOOST_OUTCOME_TRY(header.transactions_root, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(header.difficulty, decode_unsigned<uint256_t>(payload));
    BOOST_OUTCOME_TRY(header.number, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(header.gas_limit, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(header.timestamp, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(header.extra_data, decode_string(payload));
    BOOST_OUTCOME_TRY(header.prev_randao, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(header.nonce, decode_byte_string_fixed<8>(payload));
    BOOST_OUTCOME_TRY(
        header.base_fee_per_gas, decode_unsigned<uint256_t>(payload));
    BOOST_OUTCOME_TRY(header.withdrawals_root, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(header.blob_gas_used, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(
        header.excess_blob_gas, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(header.parent_beacon_block_root, decode_bytes32(payload));

    // TODO: This backwards-compatible logic should be temporary. When explicit
    // versioning is added to this module, the following field needs to be
    // parsed only if we're in a revision where EVMC_PRAGUE is active
    // (MONAD_FOUR and onwards).
    if (payload.size() > 0) {
        BOOST_OUTCOME_TRY(header.requests_hash, decode_bytes32(payload));
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return header;
}

Result<std::vector<BlockHeader>> decode_execution_results(byte_string_view &enc)
{
    std::vector<BlockHeader> headers;

    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));
    while (!payload.empty()) {
        BOOST_OUTCOME_TRY(auto header, decode_block_header(payload));
        headers.emplace_back(std::move(header));
    }
    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return headers;
}

template <class MonadQuorumCertificate>
Result<MonadQuorumCertificate> decode_quorum_certificate(byte_string_view &enc)
{
    MonadQuorumCertificate qc;

    BOOST_OUTCOME_TRY(auto qc_payload, parse_list_metadata(enc));
    BOOST_OUTCOME_TRY(auto vote_payload, parse_list_metadata(qc_payload));
    BOOST_OUTCOME_TRY(auto signatures_payload, parse_list_metadata(qc_payload));
    if (MONAD_UNLIKELY(!qc_payload.empty())) {
        return DecodeError::InputTooLong;
    }

    BOOST_OUTCOME_TRY(qc.vote.id, decode_bytes32(vote_payload));
    BOOST_OUTCOME_TRY(qc.vote.round, decode_unsigned<uint64_t>(vote_payload));
    BOOST_OUTCOME_TRY(qc.vote.epoch, decode_unsigned<uint64_t>(vote_payload));

    if constexpr (std::same_as<
                      MonadQuorumCertificate,
                      MonadQuorumCertificateV0>) {
        BOOST_OUTCOME_TRY(qc.vote.parent_id, decode_bytes32(vote_payload));
        BOOST_OUTCOME_TRY(
            qc.vote.parent_round, decode_unsigned<uint64_t>(vote_payload));
    }
    if (MONAD_UNLIKELY(!vote_payload.empty())) {
        return DecodeError::InputTooLong;
    }

    BOOST_OUTCOME_TRY(
        auto signer_map_payload, parse_list_metadata(signatures_payload));
    BOOST_OUTCOME_TRY(
        qc.signatures.signer_map.num_bits,
        decode_unsigned<uint32_t>(signer_map_payload));
    BOOST_OUTCOME_TRY(
        qc.signatures.signer_map.bitmap, decode_string(signer_map_payload));
    BOOST_OUTCOME_TRY(
        qc.signatures.aggregate_signature,
        decode_byte_string_fixed<96>(signatures_payload));
    if (MONAD_UNLIKELY(!signatures_payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return qc;
}

MONAD_RLP_ANONYMOUS_NAMESPACE_END

MONAD_RLP_NAMESPACE_BEGIN

Result<uint64_t>
decode_consensus_block_header_timestamp_s(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    // parse the timestamp
    BOOST_OUTCOME_TRY(auto _, parse_string_metadata(payload)); // round
    BOOST_OUTCOME_TRY(_, parse_string_metadata(payload)); // epoch
    BOOST_OUTCOME_TRY(_, parse_list_metadata(payload)); // qc
    BOOST_OUTCOME_TRY(_, parse_string_metadata(payload)); // author
    BOOST_OUTCOME_TRY(_, parse_string_metadata(payload)); // seqno
    BOOST_OUTCOME_TRY(
        uint128_t const timestamp_ns, decode_unsigned<uint128_t>(payload));
    return uint64_t{timestamp_ns / 1'000'000'000};
}

Result<MonadConsensusBlockBody>
decode_consensus_block_body(byte_string_view &enc)
{
    MonadConsensusBlockBody body;

    BOOST_OUTCOME_TRY(auto consensus_body_payload, parse_list_metadata(enc));
    if (MONAD_UNLIKELY(!enc.empty())) {
        return DecodeError::InputTooLong;
    }

    BOOST_OUTCOME_TRY(
        auto execution_payload, parse_list_metadata(consensus_body_payload));
    if (MONAD_UNLIKELY(!consensus_body_payload.empty())) {
        return DecodeError::InputTooLong;
    }

    BOOST_OUTCOME_TRY(
        body.transactions, decode_transaction_list(execution_payload));
    BOOST_OUTCOME_TRY(
        body.ommers, decode_block_header_vector(execution_payload));
    BOOST_OUTCOME_TRY(
        body.withdrawals, decode_withdrawal_list(execution_payload));
    if (MONAD_UNLIKELY(!execution_payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return body;
}

template <class MonadConsensusBlockHeader>
Result<MonadConsensusBlockHeader>
decode_consensus_block_header(byte_string_view &enc)
{
    MonadConsensusBlockHeader header;

    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    BOOST_OUTCOME_TRY(header.block_round, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(header.epoch, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(
        header.qc, decode_quorum_certificate<decltype(header.qc)>(payload));
    BOOST_OUTCOME_TRY(header.author, decode_byte_string_fixed<33>(payload));
    BOOST_OUTCOME_TRY(header.seqno, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(header.timestamp_ns, decode_unsigned<uint128_t>(payload));
    BOOST_OUTCOME_TRY(
        header.round_signature, decode_byte_string_fixed<96>(payload));
    BOOST_OUTCOME_TRY(
        header.delayed_execution_results, decode_execution_results(payload));
    BOOST_OUTCOME_TRY(
        header.execution_inputs, decode_execution_inputs(payload));
    BOOST_OUTCOME_TRY(header.block_body_id, decode_bytes32(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }
    return header;
}

EXPLICIT_MONAD_CONSENSUS_BLOCK_HEADER(decode_consensus_block_header);

MONAD_RLP_NAMESPACE_END
