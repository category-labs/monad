#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/result.hpp>
#include <monad/core/rlp/address_rlp.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/rlp/bytes_rlp.hpp>
#include <monad/core/rlp/int_rlp.hpp>
#include <monad/core/rlp/receipt_rlp.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/core/rlp/withdrawal_rlp.hpp>
#include <monad/core/transaction.hpp>
#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/decode_error.hpp>
#include <monad/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

#include <cstdint>
#include <optional>
#include <utility>
#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_block_header(BlockHeader const &block_header)
{
    byte_string encoded_block_header;
    encoded_block_header += encode_bytes32(block_header.parent_hash);
    encoded_block_header += encode_bytes32(block_header.ommers_hash);
    encoded_block_header += encode_address(block_header.beneficiary);
    encoded_block_header += encode_bytes32(block_header.state_root);
    encoded_block_header += encode_bytes32(block_header.transactions_root);
    encoded_block_header += encode_bytes32(block_header.receipts_root);
    encoded_block_header += encode_bloom(block_header.logs_bloom);
    encoded_block_header += encode_unsigned(block_header.difficulty);
    encoded_block_header += encode_unsigned(block_header.number);
    encoded_block_header += encode_unsigned(block_header.gas_limit);
    encoded_block_header += encode_unsigned(block_header.gas_used);
    encoded_block_header += encode_unsigned(block_header.timestamp);
    encoded_block_header += encode_string2(block_header.extra_data);
    encoded_block_header += encode_bytes32(block_header.prev_randao);
    encoded_block_header +=
        encode_string2(to_byte_string_view(block_header.nonce));

    if (block_header.base_fee_per_gas.has_value()) {
        encoded_block_header +=
            encode_unsigned(block_header.base_fee_per_gas.value());
    }

    if (block_header.withdrawals_root.has_value()) {
        encoded_block_header +=
            encode_bytes32(block_header.withdrawals_root.value());
    }

    if (block_header.blob_gas_used.has_value()) {
        encoded_block_header +=
            encode_unsigned(block_header.blob_gas_used.value());
    }
    if (block_header.excess_blob_gas.has_value()) {
        encoded_block_header +=
            encode_unsigned(block_header.excess_blob_gas.value());
    }
    if (block_header.parent_beacon_block_root.has_value()) {
        encoded_block_header +=
            encode_bytes32(block_header.parent_beacon_block_root.value());
    }

    if (block_header.requests_hash.has_value()) {
        encoded_block_header +=
            encode_bytes32(block_header.requests_hash.value());
    }

    return encode_list2(encoded_block_header);
}

byte_string encode_ommers(std::vector<BlockHeader> const &ommers)
{
    byte_string encoded;
    for (auto const &ommer : ommers) {
        encoded += rlp::encode_block_header(ommer);
    }
    return rlp::encode_list2(encoded);
}

byte_string encode_block(Block const &block)
{
    byte_string const encoded_block_header = encode_block_header(block.header);
    byte_string encoded_block_transactions;
    byte_string encoded_block_ommers;

    for (auto const &tx : block.transactions) {
        if (tx.type == TransactionType::legacy) {
            encoded_block_transactions += encode_transaction(tx);
        }
        else {
            encoded_block_transactions +=
                encode_string2(encode_transaction(tx));
        }
    }
    encoded_block_transactions = encode_list2(encoded_block_transactions);

    byte_string encoded_block;
    encoded_block += encoded_block_header;
    encoded_block += encoded_block_transactions;
    encoded_block += encode_ommers(block.ommers);

    if (block.withdrawals.has_value()) {
        byte_string encoded_block_withdrawals;
        for (auto const &withdraw : block.withdrawals.value()) {
            encoded_block_withdrawals += encode_withdrawal(withdraw);
        }
        encoded_block += encode_list2(encoded_block_withdrawals);
    }

    return encode_list2(encoded_block);
}

Result<BlockHeader> decode_block_header(byte_string_view &enc)
{
    BlockHeader block_header;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    BOOST_OUTCOME_TRY(block_header.parent_hash, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(block_header.ommers_hash, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(block_header.beneficiary, decode_address(payload));
    BOOST_OUTCOME_TRY(block_header.state_root, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(block_header.transactions_root, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(block_header.receipts_root, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(block_header.logs_bloom, decode_bloom(payload));
    BOOST_OUTCOME_TRY(
        block_header.difficulty, decode_unsigned<uint256_t>(payload));
    BOOST_OUTCOME_TRY(block_header.number, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(
        block_header.gas_limit, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(
        block_header.gas_used, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(
        block_header.timestamp, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(block_header.extra_data, decode_string(payload));
    BOOST_OUTCOME_TRY(block_header.prev_randao, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(block_header.nonce, decode_byte_string_fixed<8>(payload));

    if (payload.size() > 0) {
        BOOST_OUTCOME_TRY(
            block_header.base_fee_per_gas, decode_unsigned<uint256_t>(payload));
        if (payload.size() > 0) {
            BOOST_OUTCOME_TRY(
                block_header.withdrawals_root, decode_bytes32(payload));
            if (payload.size() > 0) {
                BOOST_OUTCOME_TRY(
                    block_header.blob_gas_used,
                    decode_unsigned<uint64_t>(payload));
                BOOST_OUTCOME_TRY(
                    block_header.excess_blob_gas,
                    decode_unsigned<uint64_t>(payload));
                BOOST_OUTCOME_TRY(
                    block_header.parent_beacon_block_root,
                    decode_bytes32(payload));

                if (payload.size() > 0) {
                    BOOST_OUTCOME_TRY(
                        block_header.requests_hash, decode_bytes32(payload));
                }
            }
        }
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return block_header;
}

Result<std::vector<BlockHeader>>
decode_block_header_vector(byte_string_view &enc)
{
    std::vector<BlockHeader> ommers;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    while (payload.size() > 0) {
        BOOST_OUTCOME_TRY(auto ommer, decode_block_header(payload));
        ommers.emplace_back(std::move(ommer));
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return ommers;
}

Result<Block> decode_block(byte_string_view &enc)
{
    Block block;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    BOOST_OUTCOME_TRY(block.header, decode_block_header(payload));
    BOOST_OUTCOME_TRY(block.transactions, decode_transaction_list(payload));
    BOOST_OUTCOME_TRY(block.ommers, decode_block_header_vector(payload));

    if (payload.size() > 0) {
        BOOST_OUTCOME_TRY(auto withdrawals, decode_withdrawal_list(payload));
        block.withdrawals.emplace(std::move(withdrawals));
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return block;
}

Result<Block> decode_block_with_tx_sender(byte_string_view &enc)
{
    Block block;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    BOOST_OUTCOME_TRY(block.header, decode_block_header(payload));
    BOOST_OUTCOME_TRY(
        block.transactions, decode_transaction_list_with_sender(payload));
    BOOST_OUTCOME_TRY(block.ommers, decode_block_header_vector(payload));

    if (payload.size() > 0) {
        BOOST_OUTCOME_TRY(auto withdrawals, decode_withdrawal_list(payload));
        block.withdrawals.emplace(std::move(withdrawals));
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return block;
}

MONAD_RLP_NAMESPACE_END
