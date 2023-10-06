#include <monad/rlp/decode_helpers.hpp>

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>

MONAD_RLP_NAMESPACE_BEGIN

template <size_t N>
byte_string_view
decode_byte_string_fixed(byte_string_fixed<N> &data, byte_string_view const enc)
{
    return decode_byte_array<N>(data.data(), enc);
}

byte_string_view decode_sc(SignatureAndChain &sc, byte_string_view const enc)
{
    uint64_t v{};
    auto const rest_of_enc = decode_unsigned<uint64_t>(v, enc);

    sc.from_v(v);
    return rest_of_enc;
}

byte_string_view decode_access_entry_keys(
    std::vector<bytes32_t> &keys, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);
    const byte_string_loc key_size =
        33; // 1 byte for header, 32 bytes for byte32_t
    const byte_string_loc list_space = payload.size();
    MONAD_ASSERT(keys.size() == 0);
    keys.reserve(list_space / key_size);

    while (payload.size() > 0) {
        bytes32_t key{};
        payload = decode_bytes32(key, payload);
        keys.emplace_back(key);
    }

    MONAD_ASSERT(list_space == keys.size() * key_size);
    return rest_of_enc;
}

byte_string_view
decode_access_entry(Transaction::AccessEntry &ae, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);

    payload = decode_address(ae.a, payload);
    payload = decode_access_entry_keys(ae.keys, payload);

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view
decode_access_list(Transaction::AccessList &al, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);
    const byte_string_loc approx_num_keys = 10;
    // 20 bytes for address, 33 bytes per key
    const byte_string_loc access_entry_size_approx = 20 + 33 * approx_num_keys;
    const byte_string_loc list_space = payload.size();
    MONAD_ASSERT(al.size() == 0);
    al.reserve(list_space / access_entry_size_approx);

    while (payload.size() > 0) {
        Transaction::AccessEntry ae{};
        payload = decode_access_entry(ae, payload);
        al.emplace_back(ae);
    }

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view decode_bloom(Receipt::Bloom &bloom, byte_string_view const enc)
{
    return decode_byte_array<256>(bloom.data(), enc);
}

byte_string_view
decode_topics(std::vector<bytes32_t> &topics, byte_string_view enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);
    const byte_string_loc topic_size =
        33; // 1 byte for header, 32 bytes for byte32_t
    const byte_string_loc list_space = payload.size();
    MONAD_ASSERT(topics.size() == 0);
    topics.reserve(list_space / topic_size);

    while (payload.size() > 0) {
        bytes32_t topic{};
        payload = decode_bytes32(topic, payload);
        topics.emplace_back(topic);
    }

    MONAD_ASSERT(list_space == topics.size() * topic_size);
    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view decode_log(Receipt::Log &log, byte_string_view enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);
    payload = decode_address(log.address, payload);
    payload = decode_topics(log.topics, payload);
    payload = decode_string(log.data, payload);

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view
decode_logs(std::vector<Receipt::Log> &logs, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);
    const byte_string_loc approx_data_size = 32;
    const byte_string_loc approx_num_topics = 10;
    // 20 bytes for address, 33 bytes per topic
    const byte_string_loc log_size_approx =
        20 + approx_data_size + 33 * approx_num_topics;
    const byte_string_loc list_space = payload.size();
    MONAD_ASSERT(logs.size() == 0);
    logs.resize(list_space / log_size_approx);

    while (payload.size() > 0) {
        Receipt::Log log{};
        payload = decode_log(log, payload);
        logs.emplace_back(log);
    }

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view decode_account(
    Account &acc, bytes32_t &storage_root, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);

    payload = decode_unsigned<uint64_t>(acc.nonce, payload);
    payload = decode_unsigned<uint256_t>(acc.balance, payload);
    payload = decode_bytes32(storage_root, payload);
    payload = decode_bytes32(acc.code_hash, payload);

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view
decode_transaction_legacy(Transaction &txn, byte_string_view const enc)
{
    MONAD_ASSERT(enc.size() > 0);
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);

    txn.type = TransactionType::eip155;
    payload = decode_unsigned<uint64_t>(txn.nonce, payload);
    payload = decode_unsigned<uint256_t>(txn.max_fee_per_gas, payload);
    payload = decode_unsigned<uint64_t>(txn.gas_limit, payload);
    payload = decode_address(txn.to, payload);
    payload = decode_unsigned<uint128_t>(txn.amount, payload);
    payload = decode_string(txn.data, payload);
    payload = decode_sc(txn.sc, payload);
    payload = decode_unsigned<uint256_t>(txn.sc.r, payload);
    payload = decode_unsigned<uint256_t>(txn.sc.s, payload);
    txn.from = std::nullopt;

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view
decode_transaction_eip2930(Transaction &txn, byte_string_view const enc)
{
    MONAD_ASSERT(enc.size() > 0);
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);

    txn.type = TransactionType::eip2930;
    txn.sc.chain_id = uint64_t{};
    payload = decode_unsigned<uint64_t>(*txn.sc.chain_id, payload);
    payload = decode_unsigned<uint64_t>(txn.nonce, payload);
    payload = decode_unsigned<uint256_t>(txn.max_fee_per_gas, payload);
    payload = decode_unsigned<uint64_t>(txn.gas_limit, payload);
    payload = decode_address(txn.to, payload);
    payload = decode_unsigned<uint128_t>(txn.amount, payload);
    payload = decode_string(txn.data, payload);
    payload = decode_access_list(txn.access_list, payload);
    payload = decode_bool(txn.sc.odd_y_parity, payload);
    payload = decode_unsigned<uint256_t>(txn.sc.r, payload);
    payload = decode_unsigned<uint256_t>(txn.sc.s, payload);
    txn.from = std::nullopt;

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view
decode_transaction_eip1559(Transaction &txn, byte_string_view const enc)
{
    MONAD_ASSERT(enc.size() > 0);
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);

    txn.type = TransactionType::eip1559;
    txn.sc.chain_id = uint64_t{};
    payload = decode_unsigned<uint64_t>(*txn.sc.chain_id, payload);
    payload = decode_unsigned<uint64_t>(txn.nonce, payload);
    payload = decode_unsigned<uint256_t>(txn.max_priority_fee_per_gas, payload);
    payload = decode_unsigned<uint256_t>(txn.max_fee_per_gas, payload);
    payload = decode_unsigned<uint64_t>(txn.gas_limit, payload);
    payload = decode_address(txn.to, payload);
    payload = decode_unsigned<uint128_t>(txn.amount, payload);
    payload = decode_string(txn.data, payload);
    payload = decode_access_list(txn.access_list, payload);
    payload = decode_bool(txn.sc.odd_y_parity, payload);
    payload = decode_unsigned<uint256_t>(txn.sc.r, payload);
    payload = decode_unsigned<uint256_t>(txn.sc.s, payload);
    txn.from = std::nullopt;

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view
decode_transaction(Transaction &txn, byte_string_view const enc)
{
    MONAD_ASSERT(enc.size() > 0);

    uint8_t const &first = enc[0];
    if (first < 0xc0) // eip 2718 - typed transaction envelope
    {
        byte_string_view payload{};
        auto const rest_of_enc = parse_string_metadata(payload, enc);
        MONAD_ASSERT(payload.size() > 0);

        uint8_t const &type = payload[0];
        auto const txn_enc = payload.substr(1, payload.size() - 1);

        byte_string_view (*decoder)(Transaction &, byte_string_view const);
        switch (type) {
        case 0x1:
            decoder = &decode_transaction_eip2930;
            break;
        case 0x2:
            decoder = &decode_transaction_eip1559;
            break;
        default:
            MONAD_ASSERT(false); // invalid transaction type
            return {};
        }
        auto const rest_of_txn_enc = decoder(txn, txn_enc);
        MONAD_ASSERT(rest_of_txn_enc.size() == 0);
        return rest_of_enc;
    }
    return decode_transaction_legacy(txn, enc);
}

byte_string_view
decode_untyped_receipt(Receipt &receipt, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);
    payload = decode_unsigned<uint64_t>(receipt.status, payload);
    payload = decode_unsigned<uint64_t>(receipt.gas_used, payload);
    payload = decode_bloom(receipt.bloom, payload);
    payload = decode_logs(receipt.logs, payload);

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view decode_receipt(Receipt &receipt, byte_string_view const enc)
{
    MONAD_ASSERT(enc.size() > 0);

    uint8_t const &first = enc[0];
    receipt.type = TransactionType::eip155;
    if (first < 0xc0) // eip 2718 - typed transaction envelope
    {
        byte_string_view payload{};
        auto const rest_of_enc = parse_string_metadata(payload, enc);
        MONAD_ASSERT(payload.size() > 0);

        uint8_t const &type = payload[0];
        auto const receipt_enc = payload.substr(1, payload.size() - 1);
        switch (type) {
        case 0x1:
            receipt.type = TransactionType::eip2930;
            break;
        case 0x2:
            receipt.type = TransactionType::eip1559;
            break;
        default:
            MONAD_ASSERT(false); // invalid transaction type
            return {};
        }
        auto const rest_of_receipt_enc =
            decode_untyped_receipt(receipt, receipt_enc);
        MONAD_ASSERT(rest_of_receipt_enc.size() == 0);
        return rest_of_enc;
    }
    return decode_untyped_receipt(receipt, enc);
}

byte_string_view
decode_withdrawal(Withdrawal &withdrawal, byte_string_view const enc)
{
    if (enc.size() == 0)
        return {};
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);

    payload = decode_unsigned<uint64_t>(withdrawal.index, payload);
    payload = decode_unsigned<uint64_t>(withdrawal.validator_index, payload);
    payload = decode_address(withdrawal.recipient, payload);
    payload = decode_unsigned<uint64_t>(withdrawal.amount, payload);

    MONAD_DEBUG_ASSERT(withdrawal.amount > 0);
    MONAD_DEBUG_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view decode_withdrawal_list(
    std::vector<Withdrawal> &withdrawal_list, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);

    withdrawal_list.reserve(payload.size() / sizeof(Withdrawal));

    while (payload.size() > 0) {
        Withdrawal withdrawal{};
        payload = decode_withdrawal(withdrawal, payload);
        withdrawal_list.emplace_back(withdrawal);
    }

    MONAD_DEBUG_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view
decode_block_header(BlockHeader &bh, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);

    payload = decode_bytes32(bh.parent_hash, payload);
    payload = decode_bytes32(bh.ommers_hash, payload);
    payload = decode_address(bh.beneficiary, payload);
    payload = decode_bytes32(bh.state_root, payload);
    payload = decode_bytes32(bh.transactions_root, payload);
    payload = decode_bytes32(bh.receipts_root, payload);
    payload = decode_bloom(bh.logs_bloom, payload);
    payload = decode_unsigned<uint256_t>(bh.difficulty, payload);
    payload = decode_unsigned<uint64_t>(bh.number, payload);
    payload = decode_unsigned<uint64_t>(bh.gas_limit, payload);
    payload = decode_unsigned<uint64_t>(bh.gas_used, payload);
    payload = decode_unsigned<uint64_t>(bh.timestamp, payload);
    payload = decode_string(bh.extra_data, payload);
    payload = decode_bytes32(bh.prev_randao, payload);
    payload = decode_byte_string_fixed<8>(bh.nonce, payload);
    if (payload.size() > 0) {
        uint64_t base_fee_per_gas{};
        payload = decode_unsigned<uint64_t>(base_fee_per_gas, payload);
        bh.base_fee_per_gas.emplace(base_fee_per_gas);
        if (payload.size() > 0) {
            bytes32_t withdrawal_root{};
            payload = decode_bytes32(withdrawal_root, payload);
            bh.withdrawals_root.emplace(withdrawal_root);
        }
        else {
            bh.withdrawals_root = std::nullopt;
        }
    }
    else {
        bh.base_fee_per_gas = std::nullopt;
    }

    MONAD_DEBUG_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view decode_transaction_vector(
    std::vector<Transaction> &txns, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);
    // glee: based on etherscan.io... eventually in CONFIG file
    const byte_string_loc approx_num_transactions = 300;
    MONAD_ASSERT(txns.size() == 0);
    txns.reserve(approx_num_transactions);

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
    // glee: upper bound is 2... no reserve
    MONAD_ASSERT(ommers.size() == 0);

    while (payload.size() > 0) {
        BlockHeader ommer{};
        payload = decode_block_header(ommer, payload);
        ommers.emplace_back(ommer);
    }

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view
get_rlp_header_from_block(byte_string_view const block_encoding)
{
    byte_string_view rlp_block{};
    (void)parse_list_metadata(rlp_block, block_encoding);
    byte_string_view rlp_block_header{};
    (void)parse_list_metadata(rlp_block_header, rlp_block);
    return {rlp_block.data(), rlp_block_header.end()};
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

MONAD_RLP_NAMESPACE_END
