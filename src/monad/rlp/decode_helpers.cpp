#include <monad/rlp/decode_helpers.hpp>

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/receipt.hpp>
#include <monad/core/signature.hpp>
#include <monad/core/transaction.hpp>

#include <numeric>
#include <string>

MONAD_RLP_NAMESPACE_BEGIN

// glee for glee: TODO generalize vector decoding

// glee for shea: is memcpy appropriate for various functions below?

template <size_t N>
inline byte_string_fixed<N> decode_byte_string_fixed(byte_string_view const enc, byte_string_loc &i) {
    auto dec = decode_string(enc, i);
    MONAD_ASSERT(dec.size() == N);

    byte_string_fixed<N> res;
    memcpy(res.data(), dec.data(), N);

    return res;
}

SignatureAndChain decode_sc(byte_string_view const enc, byte_string_loc &i) {
    auto dec = decode_unsigned<uint64_t>(enc, i);

    SignatureAndChain res;
    from_v(res, dec);

    return res;
}

byte_string_loc end_of_list_encoding(byte_string_view const enc, byte_string_loc &i)
{
    MONAD_ASSERT(i < enc.size());

    byte_string_loc length;
    const uint8_t &first = enc[i];
    ++i;
    MONAD_ASSERT(first >= 192);
    if (first < 248)
    {
        length = first - 192;
    }
    else
    {
        byte_string_loc length_of_length;
        length_of_length = first - 247;
        MONAD_ASSERT(i + length_of_length < enc.size());

        length = decode_length(enc, i, length_of_length);
        i += length_of_length;
    }
    const byte_string_loc end = i + length;
    MONAD_ASSERT(end <= enc.size());

    return end;
}

std::vector<bytes32_t> decode_access_entry_keys(byte_string_view const enc, byte_string_loc &i)
{
    const byte_string_loc end = end_of_list_encoding(enc, i);
    const byte_string_loc key_size = 33;    // 1 byte for header, 32 bytes for byte32_t
    const byte_string_loc list_space = end - i;
    std::vector<bytes32_t> keys;
    keys.reserve(list_space / key_size);

    while (i < end)
    {
        bytes32_t key = decode_bytes32(enc, i);
        keys.emplace_back(key);
    }

    MONAD_ASSERT(i == end);
    MONAD_ASSERT(list_space == keys.size() * key_size);
    return keys;
}

Transaction::AccessEntry decode_access_entry(byte_string_view const enc, byte_string_loc &i)
{
    const byte_string_loc end = end_of_list_encoding(enc, i);
    Transaction::AccessEntry ae;
    
    ae.a = decode_address(enc, i);
    ae.keys = decode_access_entry_keys(enc, i);

    MONAD_ASSERT(i == end);
    return ae;
}

Transaction::AccessList decode_access_list(byte_string_view const enc, byte_string_loc &i)
{
    const byte_string_loc end = end_of_list_encoding(enc, i);
    // glee for shea: totally arbitrary number... maybe you can come up with a better estimate?
    const byte_string_loc approx_num_keys = 10;
    // 20 bytes for address, 33 bytes per key
    const byte_string_loc access_entry_size_approx = 20 + 33 * approx_num_keys;
    const byte_string_loc list_space = end - i;
    Transaction::AccessList al;
    al.reserve(list_space / access_entry_size_approx);
    
    while (i < end)
    {
        al.emplace_back(decode_access_entry(enc, i));
    }

    MONAD_ASSERT(i == end);
    return al;
}

Receipt::Bloom decode_bloom(byte_string_view const enc, byte_string_loc& i){
    auto decoding = decode_string(enc, i);
    MONAD_ASSERT(decoding.size() == 256);

    Receipt::Bloom res;
    memcpy(res.data(), decoding.data(), 256);

    return res;
}

std::vector<bytes32_t> decode_topics(byte_string_view enc, byte_string_loc& i){
   // @tzhi: Maybe need to do the reserve thing here too?
    std::vector<bytes32_t> topics;
    const byte_string_loc end = end_of_list_encoding(enc, i);
    while(i < end){
        topics.emplace_back(decode_bytes32(enc,i));
    }

    MONAD_ASSERT(i == end);
    return topics;
}

// @tzhi: why do we encode data as list?
byte_string decode_log_data(byte_string_view enc, byte_string_loc& i){
    const byte_string_loc end = end_of_list_encoding(enc, i);

    byte_string data;

    while(i < end){
        data += enc[i++];
    }

    return data;
}

Receipt::Log decode_log(byte_string_view enc, byte_string_loc& i){
    Receipt::Log log;
    const byte_string_loc end = end_of_list_encoding(enc, i);
    log.address = decode_address(enc,i);
    log.topics = decode_topics(enc,i);
    log.data = decode_log_data(enc,i);

    MONAD_ASSERT(i == end);

    return log;
}



std::vector<Receipt::Log> decode_logs(byte_string_view const enc, byte_string_loc& i){
    const byte_string_loc end = end_of_list_encoding(enc, i);
    std::vector<Receipt::Log> logs;
    while(i < end){
        logs.emplace_back(decode_log(enc,i));
    }

    MONAD_ASSERT(i == end);
    return logs;
}

std::pair<Account, bytes32_t> decode_account(byte_string_view const enc, byte_string_loc &i)
{
    const byte_string_loc end = end_of_list_encoding(enc, i);
    Account acc;
    bytes32_t code_root;
    
    acc.nonce = decode_unsigned<uint64_t>(enc, i);
    acc.balance = decode_unsigned<uint256_t>(enc, i);
    code_root = decode_bytes32(enc, i);
    acc.code_hash = decode_bytes32(enc, i);

    MONAD_ASSERT(i == end);
    return std::make_pair(acc, code_root);
}

Transaction decode_transaction(byte_string_view const enc, byte_string_loc &i)
{
    MONAD_ASSERT(i < enc.size());
    Transaction txn;

    // Transaction type matching
    const uint8_t &type = enc[i];
    if (type == 0x01)       // eip2930
    {
        ++i;
        txn.type = Transaction::Type::eip2930;
    }
    else if (type == 0x02)  // eip1559
    {
        ++i;
        txn.type = Transaction::Type::eip1559;
    }
    else                    // eip155
    {
        txn.type = Transaction::Type::eip155;
    }

    const byte_string_loc end = end_of_list_encoding(enc, i);
    if (txn.type == Transaction::Type::eip155)
    {
        txn.nonce = decode_unsigned<uint64_t>(enc, i);
        printf("nonce: %lu\n", txn.nonce);
        txn.gas_price = decode_unsigned<uint64_t>(enc, i);
        printf("price: %lu\n", txn.gas_price);
        txn.gas_limit = decode_unsigned<uint64_t>(enc, i);
        printf("limit: %lu\n", txn.gas_limit);
        *txn.to = decode_address(enc, i);

        printf("to: 0x");
        for (size_t i = 0; i < 20; ++i) {
            printf("%.2x", (*txn.to).bytes[i]);
        }
        printf("\n");

        txn.amount = decode_unsigned<uint128_t>(enc, i);
        printf("amount: %llu\n", (unsigned long long)txn.amount);
        txn.data = decode_string(enc, i);
        txn.sc = decode_sc(enc, i);
        txn.sc.r = decode_unsigned<uint256_t>(enc, i);
        txn.sc.s = decode_unsigned<uint256_t>(enc, i);
    }
    else if (txn.type == Transaction::Type::eip1559)
    {
        *txn.sc.chain_id = decode_unsigned<uint64_t>(enc, i);
        txn.nonce = decode_unsigned<uint64_t>(enc, i);
        txn.priority_fee = decode_unsigned<uint64_t>(enc, i);
        txn.gas_price = decode_unsigned<uint64_t>(enc, i);
        txn.gas_limit = decode_unsigned<uint64_t>(enc, i);
        *txn.to = decode_address(enc, i);
        txn.amount = decode_unsigned<uint128_t>(enc, i);
        txn.data = decode_string(enc, i);
        txn.access_list = decode_access_list(enc, i);
        txn.sc.odd_y_parity = decode_unsigned<bool>(enc, i);
        txn.sc.r = decode_unsigned<uint256_t>(enc, i);
        txn.sc.s = decode_unsigned<uint256_t>(enc, i);
    }
    else            // Transaction::type::eip2930
    {
        *txn.sc.chain_id = decode_unsigned<uint64_t>(enc, i);
        txn.nonce = decode_unsigned<uint64_t>(enc, i);
        txn.gas_price = decode_unsigned<uint64_t>(enc, i);
        txn.gas_limit = decode_unsigned<uint64_t>(enc, i);
        *txn.to = decode_address(enc, i);
        txn.amount = decode_unsigned<uint128_t>(enc, i);
        txn.data = decode_string(enc, i);
        txn.access_list = decode_access_list(enc, i);
        txn.sc.odd_y_parity = decode_unsigned<bool>(enc, i);
        txn.sc.r = decode_unsigned<uint256_t>(enc, i);
        txn.sc.s = decode_unsigned<uint256_t>(enc, i);
    }
    txn.from = std::nullopt;

    MONAD_ASSERT(i == end);
    return txn;
}

Receipt decode_receipt(byte_string_view const enc, byte_string_loc& i){
    unsigned prefix = enc[i];
    Receipt receipt;
    if (prefix == 0x01){
        receipt.type = Transaction::Type::eip1559;
        ++i;
    } else if(prefix == 0x02){
        receipt.type = Transaction::Type::eip2930;
        ++i;
    }else {
        receipt.type = Transaction::Type::eip155;
    }

    const byte_string_loc end = end_of_list_encoding(enc, i);
    receipt.status = decode_unsigned<uint64_t>(enc, i);
    receipt.gas_used = decode_unsigned<uint64_t>(enc,i);
    receipt.bloom = decode_bloom(enc,i);
    receipt.logs = decode_logs(enc,i);

    MONAD_ASSERT(i == end);
    return receipt;
}


inline BlockHeader decode_block_header(byte_string_view const enc, byte_string_loc &i)
{
    const byte_string_loc end = end_of_list_encoding(enc, i);
    BlockHeader block_header;

    block_header.parent_hash = decode_bytes32(enc, i);
    block_header.ommers_hash = decode_bytes32(enc, i);
    block_header.beneficiary = decode_address(enc, i);
    block_header.state_root = decode_bytes32(enc, i);
    block_header.transactions_root = decode_bytes32(enc, i);
    block_header.receipts_root = decode_bytes32(enc, i);
    block_header.logs_bloom = decode_bloom(enc, i);
    block_header.difficulty = decode_unsigned<uint256_t>(enc, i);
    block_header.number = decode_unsigned<uint64_t>(enc, i);
    block_header.gas_limit = decode_unsigned<uint64_t>(enc, i);
    block_header.gas_used = decode_unsigned<uint64_t>(enc, i);
    block_header.timestamp = decode_unsigned<uint64_t>(enc, i);
    block_header.extra_data = decode_string(enc, i);
    block_header.mix_hash = decode_bytes32(enc, i);
    block_header.nonce = decode_byte_string_fixed<8>(enc, i);
    if (i != end)
    {
        block_header.base_fee_per_gas = decode_unsigned<uint256_t>(enc, i);
    }
    else
    {
        block_header.base_fee_per_gas = std::nullopt;
    }

    MONAD_ASSERT(i == end);
    return block_header;
}

// glee for glee: TODO reserve vector size to avoid extra allocation
inline std::vector<Transaction> decode_transaction_vector(byte_string_view const enc, byte_string_loc &i)
{
    const byte_string_loc end = end_of_list_encoding(enc, i);
    std::vector<Transaction> txns;
    
    while (i < end)
    {
        txns.emplace_back(decode_transaction(enc, i));
    }

    MONAD_ASSERT(i == end);
    return txns;
}

// glee for glee: TODO reserve vector size to avoid extra allocation
inline std::vector<BlockHeader> decode_block_header_vector(byte_string_view const enc, byte_string_loc &i)
{
    const byte_string_loc end = end_of_list_encoding(enc, i);
    std::vector<BlockHeader> ommers;
    
    while (i < end)
    {
        ommers.emplace_back(decode_block_header(enc, i));
    }

    MONAD_ASSERT(i == end);
    return ommers;
}

Block decode_block(byte_string_view const enc, byte_string_loc &i)
{
    const byte_string_loc end = end_of_list_encoding(enc, i);
    Block block;
    
    block.header = decode_block_header(enc, i);
    printf("1\n");
    block.transactions = decode_transaction_vector(enc, i);
    printf("2\n");
    block.ommers = decode_block_header_vector(enc, i);

    MONAD_ASSERT(i == end);
    return block;
}

MONAD_RLP_NAMESPACE_END