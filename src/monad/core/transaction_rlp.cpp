#include <monad/core/address_rlp.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/bytes_rlp.hpp>
#include <monad/core/int.hpp>
#include <monad/core/int_rlp.hpp>
#include <monad/core/signature.hpp>
#include <monad/core/signature_rlp.hpp>
#include <monad/core/transaction.hpp>
#include <monad/core/transaction_rlp.hpp>
#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/encode2.hpp>

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

// Encode
byte_string encode_access_list(AccessList const &access_list)
{
    byte_string result;
    byte_string temp;
    for (auto const &[addr, keys] : access_list) {
        temp.clear();
        for (auto const &key : keys) {
            temp += encode_bytes32(key);
        }
        result += encode_list2(encode_address(addr) + encode_list2(temp));
    };

    return encode_list2(result);
}

byte_string encode_transaction(Transaction const &txn)
{
    if (txn.type == TransactionType::eip155) {
        return encode_list2(
            encode_unsigned(txn.nonce),
            encode_unsigned(txn.max_fee_per_gas),
            encode_unsigned(txn.gas_limit),
            encode_address(txn.to),
            encode_unsigned(txn.value),
            encode_string2(txn.data),
            encode_unsigned(get_v(txn.sc)),
            encode_unsigned(txn.sc.r),
            encode_unsigned(txn.sc.s));
    }

    MONAD_ASSERT(txn.sc.chain_id != std::nullopt);

    if (txn.type == TransactionType::eip1559) {
        return encode_string2(
            byte_string{0x02} += encode_list2(
                encode_unsigned(txn.sc.chain_id.value_or(0)),
                encode_unsigned(txn.nonce),
                encode_unsigned(txn.max_priority_fee_per_gas),
                encode_unsigned(txn.max_fee_per_gas),
                encode_unsigned(txn.gas_limit),
                encode_address(txn.to),
                encode_unsigned(txn.value),
                encode_string2(txn.data),
                encode_access_list(txn.access_list),
                encode_unsigned(static_cast<unsigned>(txn.sc.odd_y_parity)),
                encode_unsigned(txn.sc.r),
                encode_unsigned(txn.sc.s)));
    }
    else if (txn.type == TransactionType::eip2930) {
        return encode_string2(
            byte_string{0x01} += encode_list2(
                encode_unsigned(txn.sc.chain_id.value_or(0)),
                encode_unsigned(txn.nonce),
                encode_unsigned(txn.max_fee_per_gas),
                encode_unsigned(txn.gas_limit),
                encode_address(txn.to),
                encode_unsigned(txn.value),
                encode_string2(txn.data),
                encode_access_list(txn.access_list),
                encode_unsigned(static_cast<unsigned>(txn.sc.odd_y_parity)),
                encode_unsigned(txn.sc.r),
                encode_unsigned(txn.sc.s)));
    }
    assert(false);
    return {};
}

byte_string encode_transaction_for_signing(Transaction const &txn)
{
    if (txn.type == TransactionType::eip155) {
        if (txn.sc.chain_id.has_value()) {
            return encode_list2(
                encode_unsigned(txn.nonce),
                encode_unsigned(txn.max_fee_per_gas),
                encode_unsigned(txn.gas_limit),
                encode_address(txn.to),
                encode_unsigned(txn.value),
                encode_string2(txn.data),
                encode_unsigned(txn.sc.chain_id.value_or(0)),
                encode_unsigned(0u),
                encode_unsigned(0u));
        }
        else {
            return encode_list2(
                encode_unsigned(txn.nonce),
                encode_unsigned(txn.max_fee_per_gas),
                encode_unsigned(txn.gas_limit),
                encode_address(txn.to),
                encode_unsigned(txn.value),
                encode_string2(txn.data));
        }
    }

    MONAD_ASSERT(txn.sc.chain_id != std::nullopt);

    if (txn.type == TransactionType::eip1559) {
        return byte_string{0x02} +
               encode_list2(
                   encode_unsigned(txn.sc.chain_id.value_or(0)),
                   encode_unsigned(txn.nonce),
                   encode_unsigned(txn.max_priority_fee_per_gas),
                   encode_unsigned(txn.max_fee_per_gas),
                   encode_unsigned(txn.gas_limit),
                   encode_address(txn.to),
                   encode_unsigned(txn.value),
                   encode_string2(txn.data),
                   encode_access_list(txn.access_list));
    }
    else if (txn.type == TransactionType::eip2930) {
        return byte_string{0x01} +
               encode_list2(
                   encode_unsigned(txn.sc.chain_id.value_or(0)),
                   encode_unsigned(txn.nonce),
                   encode_unsigned(txn.max_fee_per_gas),
                   encode_unsigned(txn.gas_limit),
                   encode_address(txn.to),
                   encode_unsigned(txn.value),
                   encode_string2(txn.data),
                   encode_access_list(txn.access_list));
    }

    assert(false);
    return {};
}

// Decode
byte_string_view decode_access_entry_keys(
    std::vector<bytes32_t> &keys, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);
    constexpr size_t key_size = 33; // 1 byte for header, 32 bytes for byte32_t
    auto const list_space = payload.size();
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
decode_access_entry(AccessEntry &ae, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);

    payload = decode_address(ae.a, payload);
    payload = decode_access_entry_keys(ae.keys, payload);

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view
decode_access_list(AccessList &access_list, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);
    constexpr size_t approx_num_keys = 10;
    // 20 bytes for address, 33 bytes per key
    constexpr size_t access_entry_size_approx = 20 + 33 * approx_num_keys;
    auto const list_space = payload.size();
    MONAD_ASSERT(access_list.size() == 0);
    access_list.reserve(list_space / access_entry_size_approx);

    while (payload.size() > 0) {
        AccessEntry ae{};
        payload = decode_access_entry(ae, payload);
        access_list.emplace_back(ae);
    }

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
    payload = decode_unsigned<uint256_t>(txn.value, payload);
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
    txn.sc.chain_id = uint256_t{};
    payload = decode_unsigned<uint256_t>(*txn.sc.chain_id, payload);
    payload = decode_unsigned<uint64_t>(txn.nonce, payload);
    payload = decode_unsigned<uint256_t>(txn.max_fee_per_gas, payload);
    payload = decode_unsigned<uint64_t>(txn.gas_limit, payload);
    payload = decode_address(txn.to, payload);
    payload = decode_unsigned<uint256_t>(txn.value, payload);
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
    txn.sc.chain_id = uint256_t{};
    payload = decode_unsigned<uint256_t>(*txn.sc.chain_id, payload);
    payload = decode_unsigned<uint64_t>(txn.nonce, payload);
    payload = decode_unsigned<uint256_t>(txn.max_priority_fee_per_gas, payload);
    payload = decode_unsigned<uint256_t>(txn.max_fee_per_gas, payload);
    payload = decode_unsigned<uint64_t>(txn.gas_limit, payload);
    payload = decode_address(txn.to, payload);
    payload = decode_unsigned<uint256_t>(txn.value, payload);
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

MONAD_RLP_NAMESPACE_END
