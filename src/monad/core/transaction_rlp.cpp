#include <monad/core/address_rlp.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/bytes_rlp.hpp>
#include <monad/core/int.hpp>
#include <monad/core/int_rlp.hpp>
#include <monad/core/likely.h>
#include <monad/core/result.hpp>
#include <monad/core/signature.hpp>
#include <monad/core/signature_rlp.hpp>
#include <monad/core/transaction.hpp>
#include <monad/core/transaction_rlp.hpp>
#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/decode_error.hpp>
#include <monad/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

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

byte_string encode_legacy_base(Transaction const &txn)
{
    byte_string encoding{};

    encoding += encode_unsigned(txn.nonce);
    encoding += encode_unsigned(txn.max_fee_per_gas);
    encoding += encode_unsigned(txn.gas_limit);
    encoding += encode_address(txn.to);
    encoding += encode_unsigned(txn.value);
    encoding += encode_string2(txn.data);

    return encoding;
}

byte_string encode_eip2718_base(Transaction const &txn)
{
    byte_string encoding{};

    encoding += encode_unsigned(txn.sc.chain_id.value_or(0));
    encoding += encode_unsigned(txn.nonce);
    if (txn.type == TransactionType::eip1559) {
        encoding += encode_unsigned(txn.max_priority_fee_per_gas);
    }
    encoding += encode_unsigned(txn.max_fee_per_gas);
    encoding += encode_unsigned(txn.gas_limit);
    encoding += encode_address(txn.to);
    encoding += encode_unsigned(txn.value);
    encoding += encode_string2(txn.data);
    encoding += encode_access_list(txn.access_list);

    return encoding;
}

byte_string encode_transaction(Transaction const &txn)
{
    if (txn.type == TransactionType::legacy) {
        return encode_list2(
            encode_legacy_base(txn),
            encode_unsigned(get_v(txn.sc)),
            encode_unsigned(txn.sc.r),
            encode_unsigned(txn.sc.s));
    }
    else {
        auto const prefix = txn.type == TransactionType::eip1559
                                ? byte_string{0x02}
                                : byte_string{0x01};
        return encode_string2(
            prefix +
            encode_list2(
                encode_eip2718_base(txn),
                encode_unsigned(static_cast<unsigned>(txn.sc.odd_y_parity)),
                encode_unsigned(txn.sc.r),
                encode_unsigned(txn.sc.s)));
    }
}

byte_string encode_transaction_for_signing(Transaction const &txn)
{
    if (txn.type == TransactionType::legacy) {
        if (txn.sc.chain_id.has_value()) {
            return encode_list2(
                encode_legacy_base(txn),
                encode_unsigned(txn.sc.chain_id.value_or(0)),
                encode_unsigned(0u),
                encode_unsigned(0u));
        }
        else {
            return encode_list2(encode_legacy_base(txn));
        }
    }
    else {
        auto const prefix = txn.type == TransactionType::eip1559
                                ? byte_string{0x02}
                                : byte_string{0x01};
        return prefix + encode_list2(encode_eip2718_base(txn));
    }
}

// Decode
Result<byte_string_view> decode_access_entry_keys(
    std::vector<bytes32_t> &keys, byte_string_view const enc)
{
    byte_string_view payload{};
    BOOST_OUTCOME_TRY(
        auto const rest_of_enc, parse_list_metadata(payload, enc));
    constexpr size_t key_size = 33; // 1 byte for header, 32 bytes for byte32_t
    auto const list_space = payload.size();
    MONAD_ASSERT(keys.size() == 0);
    keys.reserve(list_space / key_size);

    while (payload.size() > 0) {
        bytes32_t key{};
        BOOST_OUTCOME_TRY(payload, decode_bytes32(key, payload));
        keys.emplace_back(key);
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    MONAD_ASSERT(list_space == keys.size() * key_size);
    return rest_of_enc;
}

Result<byte_string_view>
decode_access_entry(AccessEntry &ae, byte_string_view const enc)
{
    byte_string_view payload{};
    BOOST_OUTCOME_TRY(
        auto const rest_of_enc, parse_list_metadata(payload, enc));

    BOOST_OUTCOME_TRY(payload, decode_address(ae.a, payload));
    BOOST_OUTCOME_TRY(payload, decode_access_entry_keys(ae.keys, payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return rest_of_enc;
}

Result<byte_string_view>
decode_access_list(AccessList &access_list, byte_string_view const enc)
{
    byte_string_view payload{};
    BOOST_OUTCOME_TRY(
        auto const rest_of_enc, parse_list_metadata(payload, enc));
    constexpr size_t approx_num_keys = 10;
    // 20 bytes for address, 33 bytes per key
    constexpr size_t access_entry_size_approx = 20 + 33 * approx_num_keys;
    auto const list_space = payload.size();
    MONAD_ASSERT(access_list.size() == 0);
    access_list.reserve(list_space / access_entry_size_approx);

    while (payload.size() > 0) {
        AccessEntry ae{};
        BOOST_OUTCOME_TRY(payload, decode_access_entry(ae, payload));
        access_list.emplace_back(ae);
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return rest_of_enc;
}

Result<byte_string_view>
decode_transaction_legacy(Transaction &txn, byte_string_view const enc)
{
    byte_string_view payload{};
    BOOST_OUTCOME_TRY(
        auto const rest_of_enc, parse_list_metadata(payload, enc));

    txn.type = TransactionType::legacy;
    BOOST_OUTCOME_TRY(payload, decode_unsigned<uint64_t>(txn.nonce, payload));
    BOOST_OUTCOME_TRY(
        payload, decode_unsigned<uint256_t>(txn.max_fee_per_gas, payload));
    BOOST_OUTCOME_TRY(
        payload, decode_unsigned<uint64_t>(txn.gas_limit, payload));
    BOOST_OUTCOME_TRY(payload, decode_address(txn.to, payload));
    BOOST_OUTCOME_TRY(payload, decode_unsigned<uint256_t>(txn.value, payload));
    BOOST_OUTCOME_TRY(payload, decode_string(txn.data, payload));
    BOOST_OUTCOME_TRY(payload, decode_sc(txn.sc, payload));
    BOOST_OUTCOME_TRY(payload, decode_unsigned<uint256_t>(txn.sc.r, payload));
    BOOST_OUTCOME_TRY(payload, decode_unsigned<uint256_t>(txn.sc.s, payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return rest_of_enc;
}

Result<byte_string_view>
decode_transaction_eip2718(Transaction &txn, byte_string_view const enc)
{
    byte_string_view payload{};
    BOOST_OUTCOME_TRY(
        auto const rest_of_enc, parse_list_metadata(payload, enc.substr(1)));

    txn.type =
        enc[0] == 0x01 ? TransactionType::eip2930 : TransactionType::eip1559;

    txn.sc.chain_id = uint256_t{};
    BOOST_OUTCOME_TRY(
        payload, decode_unsigned<uint256_t>(*txn.sc.chain_id, payload));
    BOOST_OUTCOME_TRY(payload, decode_unsigned<uint64_t>(txn.nonce, payload));

    if (txn.type == TransactionType::eip1559) {
        BOOST_OUTCOME_TRY(
            payload,
            decode_unsigned<uint256_t>(txn.max_priority_fee_per_gas, payload));
    }

    BOOST_OUTCOME_TRY(
        payload, decode_unsigned<uint256_t>(txn.max_fee_per_gas, payload));
    BOOST_OUTCOME_TRY(
        payload, decode_unsigned<uint64_t>(txn.gas_limit, payload));
    BOOST_OUTCOME_TRY(payload, decode_address(txn.to, payload));
    BOOST_OUTCOME_TRY(payload, decode_unsigned<uint256_t>(txn.value, payload));
    BOOST_OUTCOME_TRY(payload, decode_string(txn.data, payload));
    BOOST_OUTCOME_TRY(payload, decode_access_list(txn.access_list, payload));
    BOOST_OUTCOME_TRY(payload, decode_bool(txn.sc.odd_y_parity, payload));
    BOOST_OUTCOME_TRY(payload, decode_unsigned<uint256_t>(txn.sc.r, payload));
    BOOST_OUTCOME_TRY(payload, decode_unsigned<uint256_t>(txn.sc.s, payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return rest_of_enc;
}

Result<byte_string_view>
decode_transaction(Transaction &txn, byte_string_view const enc)
{
    if (MONAD_UNLIKELY(enc.empty())) {
        return DecodeError::InputTooShort;
    }

    uint8_t const &first = enc[0];
    if (first < 0xc0) // eip 2718 - typed transaction envelope
    {
        byte_string_view payload{};
        BOOST_OUTCOME_TRY(
            auto const rest_of_enc, parse_string_metadata(payload, enc));
        MONAD_ASSERT(payload.size() > 0);

        uint8_t const &type = payload[0];

        if (MONAD_UNLIKELY(type != 0x01 && type != 0x02)) {
            return DecodeError::InvalidTxnType;
        }
        BOOST_OUTCOME_TRY(
            auto const rest_of_txn_enc,
            decode_transaction_eip2718(txn, payload));

        if (MONAD_UNLIKELY(!rest_of_txn_enc.empty())) {
            return DecodeError::InputTooLong;
        }

        return rest_of_enc;
    }
    return decode_transaction_legacy(txn, enc);
}

MONAD_RLP_NAMESPACE_END
