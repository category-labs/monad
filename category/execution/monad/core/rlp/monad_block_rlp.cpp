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
        header.base_fee_per_gas, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(header.withdrawals_root, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(header.blob_gas_used, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(
        header.excess_blob_gas, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(header.parent_beacon_block_root, decode_bytes32(payload));

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

byte_string encode_execution_inputs(BlockHeader const &header)
{
    byte_string encoded_inputs;
    encoded_inputs += encode_bytes32(header.ommers_hash);
    encoded_inputs += encode_address(header.beneficiary);
    encoded_inputs += encode_bytes32(header.transactions_root);
    encoded_inputs += encode_unsigned(header.difficulty);
    encoded_inputs += encode_unsigned(header.number);
    encoded_inputs += encode_unsigned(header.gas_limit);
    encoded_inputs += encode_unsigned(header.timestamp);
    encoded_inputs += encode_string2(header.extra_data);
    encoded_inputs += encode_bytes32(header.prev_randao);
    encoded_inputs += encode_string2(to_byte_string_view(header.nonce));
    encoded_inputs += encode_unsigned(header.base_fee_per_gas.value_or(0u));
    encoded_inputs +=
        encode_bytes32(header.withdrawals_root.value_or(bytes32_t{}));
    encoded_inputs += encode_unsigned(header.blob_gas_used.value_or(0u));
    encoded_inputs += encode_unsigned(header.excess_blob_gas.value_or(0u));
    encoded_inputs +=
        encode_bytes32(header.parent_beacon_block_root.value_or(bytes32_t{}));
    return encode_list2(encoded_inputs);
}

template <class MonadQuorumCertificate>
byte_string encode_quorum_certificate(MonadQuorumCertificate const &qc)
{
    byte_string vote_encoded;
    vote_encoded += encode_bytes32(qc.vote.id);
    vote_encoded += encode_unsigned(qc.vote.round);
    vote_encoded += encode_unsigned(qc.vote.epoch);

    if constexpr (std::same_as<
                      MonadQuorumCertificate,
                      MonadQuorumCertificateV0>) {
        vote_encoded += encode_bytes32(qc.vote.parent_id);
        vote_encoded += encode_unsigned(qc.vote.parent_round);
    }

    byte_string signatures_encoded;
    signatures_encoded += encode_list2(
        encode_unsigned(qc.signatures.signer_map.num_bits),
        encode_string2(qc.signatures.signer_map.bitmap));
    signatures_encoded +=
        encode_string2(to_byte_string_view(qc.signatures.aggregate_signature));

    return encode_list2(
        encode_list2(vote_encoded), encode_list2(signatures_encoded));
}

MONAD_RLP_ANONYMOUS_NAMESPACE_END

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_consensus_block_body(MonadConsensusBlockBody const &body)
{
    byte_string txns;
    for (auto const &tx : body.transactions) {
        txns += encode_transaction(tx);
    }
    byte_string withdrawals;
    for (auto const &w : body.withdrawals) {
        withdrawals += encode_withdrawal(w);
    }

    return encode_list2(encode_list2(
        encode_list2(txns),
        encode_ommers(body.ommers),
        encode_list2(withdrawals)));
}

template <class MonadConsensusBlockHeader>
byte_string
encode_consensus_block_header(MonadConsensusBlockHeader const &header)
{
    byte_string encoded_header;
    encoded_header += encode_unsigned(header.block_round);
    encoded_header += encode_unsigned(header.epoch);
    encoded_header += encode_quorum_certificate(header.qc);
    encoded_header += encode_string2(to_byte_string_view(header.author));
    encoded_header += encode_unsigned(header.seqno);
    encoded_header += encode_unsigned(header.timestamp_ns);
    encoded_header +=
        encode_string2(to_byte_string_view(header.round_signature));

    byte_string encoded_delayed_execution_results;
    for (auto const &res : header.delayed_execution_results) {
        encoded_delayed_execution_results += encode_block_header(res);
    }
    encoded_header += encode_list2(encoded_delayed_execution_results);

    encoded_header += encode_execution_inputs(header.execution_inputs);
    encoded_header += encode_bytes32(header.block_body_id);
    return encode_list2(encoded_header);
}

EXPLICIT_MONAD_CONSENSUS_BLOCK_HEADER(encode_consensus_block_header);

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
