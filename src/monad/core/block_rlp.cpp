#include <monad/core/address_rlp.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/block_rlp.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/bytes_rlp.hpp>
#include <monad/core/int.hpp>
#include <monad/core/int_rlp.hpp>
#include <monad/core/receipt_rlp.hpp>
#include <monad/core/transaction.hpp>
#include <monad/core/transaction_rlp.hpp>
#include <monad/core/withdrawal.hpp>
#include <monad/core/withdrawal_rlp.hpp>
#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/encode2.hpp>

#include <cstdint>
#include <optional>
#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

// Encode
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

    return encode_list2(encoded_block_header);
}

byte_string encode_block(Block const &block)
{
    byte_string const encoded_block_header = encode_block_header(block.header);
    byte_string encoded_block_transactions;
    byte_string encoded_block_ommers;

    for (auto const &txn : block.transactions) {
        encoded_block_transactions += encode_transaction(txn);
    }
    encoded_block_transactions = encode_list2(encoded_block_transactions);

    for (auto const &ommer : block.ommers) {
        encoded_block_ommers += encode_block_header(ommer);
    }
    encoded_block_ommers = encode_list2(encoded_block_ommers);

    byte_string encoded_block;
    encoded_block += encoded_block_header;
    encoded_block += encoded_block_transactions;
    encoded_block += encoded_block_ommers;

    if (block.withdrawals.has_value()) {
        byte_string encoded_block_withdrawals;
        for (auto const &withdraw : block.withdrawals.value()) {
            encoded_block_withdrawals += encode_withdrawal(withdraw);
        }
        encoded_block += encode_list2(encoded_block_withdrawals);
    }

    return encode_list2(encoded_block);
}

// Decode
byte_string_view
decode_block_header(BlockHeader &block_header, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);

    payload = decode_bytes32(block_header.parent_hash, payload);
    payload = decode_bytes32(block_header.ommers_hash, payload);
    payload = decode_address(block_header.beneficiary, payload);
    payload = decode_bytes32(block_header.state_root, payload);
    payload = decode_bytes32(block_header.transactions_root, payload);
    payload = decode_bytes32(block_header.receipts_root, payload);
    payload = decode_bloom(block_header.logs_bloom, payload);
    payload = decode_unsigned<uint256_t>(block_header.difficulty, payload);
    payload = decode_unsigned<uint64_t>(block_header.number, payload);
    payload = decode_unsigned<uint64_t>(block_header.gas_limit, payload);
    payload = decode_unsigned<uint64_t>(block_header.gas_used, payload);
    payload = decode_unsigned<uint64_t>(block_header.timestamp, payload);
    payload = decode_string(block_header.extra_data, payload);
    payload = decode_bytes32(block_header.prev_randao, payload);
    payload = decode_byte_string_fixed<8>(block_header.nonce, payload);
    if (payload.size() > 0) {
        uint64_t base_fee_per_gas{};
        payload = decode_unsigned<uint64_t>(base_fee_per_gas, payload);
        block_header.base_fee_per_gas.emplace(base_fee_per_gas);
        if (payload.size() > 0) {
            bytes32_t withdrawal_root{};
            payload = decode_bytes32(withdrawal_root, payload);
            block_header.withdrawals_root.emplace(withdrawal_root);
        }
        else {
            block_header.withdrawals_root = std::nullopt;
        }
    }
    else {
        block_header.base_fee_per_gas = std::nullopt;
    }

    MONAD_DEBUG_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view decode_transaction_vector(
    std::vector<Transaction> &txns, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);
    MONAD_ASSERT(txns.size() == 0);

    // TODO: Reserve txn vector size for better perf
    while (payload.size() > 0) {
        Transaction txn{};
        payload = decode_transaction(txn, payload);
        txns.emplace_back(txn);
    }

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view decode_block_header_vector(
    std::vector<BlockHeader> &ommers, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);
    MONAD_ASSERT(ommers.size() == 0);

    while (payload.size() > 0) {
        BlockHeader ommer{};
        payload = decode_block_header(ommer, payload);
        ommers.emplace_back(ommer);
    }

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view decode_block(Block &block, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);

    payload = decode_block_header(block.header, payload);
    payload = decode_transaction_vector(block.transactions, payload);
    payload = decode_block_header_vector(block.ommers, payload);

    if (payload.size() > 0) {
        std::vector<Withdrawal> withdrawals{};
        payload = decode_withdrawal_list(withdrawals, payload);
        block.withdrawals = withdrawals;
    }

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

// Get RLP Header (TODO: Why not used currently?)
byte_string_view
get_rlp_header_from_block(byte_string_view const block_encoding)
{
    byte_string_view rlp_block{};
    (void)parse_list_metadata(rlp_block, block_encoding);
    byte_string_view rlp_block_header{};
    (void)parse_list_metadata(rlp_block_header, rlp_block);
    return {rlp_block.data(), rlp_block_header.end()};
}

MONAD_RLP_NAMESPACE_END
