#include <monad/core/rlp/address_rlp.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/rlp/bytes_rlp.hpp>
#include <monad/core/rlp/monad_block_rlp.hpp>
#include <monad/core/rlp/int_rlp.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/core/rlp/withdrawal_rlp.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/decode_error.hpp>

#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

Result<BlockHeader> decode_execution_inputs(byte_string_view &enc)
{
    BlockHeader block_header;

    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));
    BOOST_OUTCOME_TRY(block_header.ommers_hash, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(block_header.beneficiary, decode_address(payload));
    BOOST_OUTCOME_TRY(block_header.transactions_root, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(
        block_header.difficulty, decode_unsigned<uint256_t>(payload));
    BOOST_OUTCOME_TRY(block_header.number, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(
        block_header.gas_limit, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(
        block_header.timestamp, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(block_header.extra_data, decode_string(payload));
    BOOST_OUTCOME_TRY(block_header.prev_randao, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(block_header.nonce, decode_byte_string_fixed<8>(payload));
    BOOST_OUTCOME_TRY(
        block_header.base_fee_per_gas, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(block_header.withdrawals_root, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(
        block_header.blob_gas_used, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(
        block_header.excess_blob_gas, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(
        block_header.parent_beacon_block_root, decode_bytes32(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return block_header;
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
    BOOST_OUTCOME_TRY(qc.vote.parent_id, decode_bytes32(vote_payload));
    BOOST_OUTCOME_TRY(
        qc.vote.parent_round, decode_unsigned<uint64_t>(vote_payload));
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

Result<MonadConsensusBlockHeader>
decode_consensus_block_header(byte_string_view &enc)
{
    MonadConsensusBlockHeader consensus_header;

    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    BOOST_OUTCOME_TRY(
        consensus_header.round, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(
        consensus_header.epoch, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(consensus_header.qc, decode_quorum_certificate(payload));
    BOOST_OUTCOME_TRY(
        consensus_header.author, decode_byte_string_fixed<33>(payload));
    BOOST_OUTCOME_TRY(
        consensus_header.seqno, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(
        consensus_header.timestamp_ns, decode_unsigned<uint128_t>(payload));
    BOOST_OUTCOME_TRY(
        consensus_header.round_signature,
        decode_byte_string_fixed<96>(payload));
    BOOST_OUTCOME_TRY(
        consensus_header.delayed_execution_results,
        decode_execution_results(payload));
    BOOST_OUTCOME_TRY(
        consensus_header.execution_inputs, decode_execution_inputs(payload));
    BOOST_OUTCOME_TRY(consensus_header.block_body_id, decode_bytes32(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }
    return consensus_header;
}

Result<MonadConsensusBlockBody> decode_consensus_block_body(byte_string_view &enc)
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

MONAD_RLP_NAMESPACE_END
