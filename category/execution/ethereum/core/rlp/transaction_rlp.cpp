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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <category/core/rlp/decode_error.hpp>
#include <category/execution/ethereum/core/rlp/address_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/signature_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/signature.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>
#include <utility>
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

byte_string
encode_authorization_entry_for_signing(AuthorizationEntry const &auth_entry)
{
    MONAD_ASSERT(auth_entry.sc.chain_id.has_value());

    byte_string result{};
    result += encode_unsigned(*auth_entry.sc.chain_id);
    result += encode_address(auth_entry.address);
    result += encode_unsigned(auth_entry.nonce);

    auto const prefix = byte_string(1, static_cast<unsigned char>(0x05));
    return prefix + encode_list2(result);
}

byte_string encode_authorization_list(AuthorizationList const &auth_list)
{
    byte_string result;

    for (auto const &auth_entry : auth_list) {
        MONAD_ASSERT(auth_entry.sc.chain_id.has_value());
        result += encode_list2(
            encode_unsigned(*auth_entry.sc.chain_id),
            encode_address(auth_entry.address),
            encode_unsigned(auth_entry.nonce),
            encode_unsigned(auth_entry.sc.signature.y_parity),
            encode_unsigned(auth_entry.sc.signature.r),
            encode_unsigned(auth_entry.sc.signature.s));
    }

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

    if (txn.type == TransactionType::eip1559 ||
        txn.type == TransactionType::eip4844 ||
        txn.type == TransactionType::eip7702) {
        encoding += encode_unsigned(txn.max_priority_fee_per_gas);
    }

    encoding += encode_unsigned(txn.max_fee_per_gas);
    encoding += encode_unsigned(txn.gas_limit);
    encoding += encode_address(txn.to);
    encoding += encode_unsigned(txn.value);
    encoding += encode_string2(txn.data);
    encoding += encode_access_list(txn.access_list);

    if (txn.type == TransactionType::eip4844) {
        encoding += encode_unsigned(txn.max_fee_per_blob_gas);
        byte_string blob_versioned_hashes;
        for (auto const &hash : txn.blob_versioned_hashes) {
            blob_versioned_hashes += encode_bytes32(hash);
        }
        encoding += encode_list2(blob_versioned_hashes);
    }

    if (txn.type == TransactionType::eip7702) {
        encoding += encode_authorization_list(txn.authorization_list);
    }

    return encoding;
}

namespace
{
    byte_string encode_monad_transaction(Transaction const &txn, bool signing)
    {
        auto const field = [](uint8_t key, byte_string const &value) {
            return encode_list2(encode_unsigned(key), value);
        };
        auto features = field(1, encode_unsigned(txn.nonce));
        features += field(2, encode_unsigned(txn.gas_limit));
        features += field(
            3,
            encode_list2(
                field(1, encode_address(txn.to)),
                field(2, encode_unsigned(txn.value)),
                field(3, encode_string2(txn.data))));
        if (txn.monad_access_list_present || !txn.access_list.empty()) {
            features += field(4, encode_access_list(txn.access_list));
        }
        features += field(
            6,
            signing ? encode_list2(byte_string{})
                    : encode_list2(
                          encode_unsigned(txn.sc.signature.y_parity),
                          encode_unsigned(txn.sc.signature.r),
                          encode_unsigned(txn.sc.signature.s)));
        features += field(
            7,
            encode_list2(
                encode_unsigned(txn.max_priority_fee_per_gas),
                encode_unsigned(txn.max_fee_per_gas)));
        return byte_string(1, 0x40) +
               encode_list2(
                   encode_unsigned(txn.sc.chain_id.value_or(0)),
                   encode_list2(features));
    }
}

byte_string encode_transaction(Transaction const &txn)
{
    if (txn.type == TransactionType::monad) {
        return encode_monad_transaction(txn, false);
    }
    if (txn.type == TransactionType::legacy) {
        return encode_list2(
            encode_legacy_base(txn),
            encode_unsigned(get_v(txn.sc)),
            encode_unsigned(txn.sc.signature.r),
            encode_unsigned(txn.sc.signature.s));
    }
    else {
        auto const prefix =
            byte_string(1, static_cast<unsigned char>(txn.type));

        return prefix + encode_list2(
                            encode_eip2718_base(txn),
                            encode_unsigned(txn.sc.signature.y_parity),
                            encode_unsigned(txn.sc.signature.r),
                            encode_unsigned(txn.sc.signature.s));
    }
}

byte_string encode_transaction_for_signing(Transaction const &txn)
{
    if (txn.type == TransactionType::monad) {
        return encode_monad_transaction(txn, true);
    }
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
        auto const prefix =
            byte_string(1, static_cast<unsigned char>(txn.type));

        return prefix + encode_list2(encode_eip2718_base(txn));
    }
}

// Decode
Result<std::vector<bytes32_t>> decode_access_entry_keys(byte_string_view &enc)
{
    std::vector<bytes32_t> keys;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));
    constexpr size_t key_size = 33; // 1 byte for header, 32 bytes for byte32_t
    auto const list_space = payload.size();
    keys.reserve(list_space / key_size);

    while (payload.size() > 0) {
        BOOST_OUTCOME_TRY(auto key, decode_bytes32(payload));
        keys.emplace_back(std::move(key));
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    MONAD_ASSERT(list_space == keys.size() * key_size);
    return keys;
}

Result<AccessEntry> decode_access_entry(byte_string_view &enc)
{
    AccessEntry access_entry;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));
    BOOST_OUTCOME_TRY(access_entry.a, decode_address(payload));
    BOOST_OUTCOME_TRY(access_entry.keys, decode_access_entry_keys(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return access_entry;
}

Result<AccessList> decode_access_list(byte_string_view &enc)
{
    AccessList access_list;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));
    constexpr size_t approx_num_keys = 10;
    // 20 bytes for address, 33 bytes per key
    constexpr size_t access_entry_size_approx = 20 + 33 * approx_num_keys;
    auto const list_space = payload.size();
    access_list.reserve(list_space / access_entry_size_approx);

    while (payload.size() > 0) {
        BOOST_OUTCOME_TRY(auto access_entry, decode_access_entry(payload));
        access_list.emplace_back(std::move(access_entry));
    }
    MONAD_ASSERT(payload.empty());

    return access_list;
}

Result<AuthorizationEntry> decode_authorization_entry(byte_string_view &enc)
{
    AuthorizationEntry auth_entry;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    auth_entry.sc.chain_id = uint256_t{};
    BOOST_OUTCOME_TRY(
        *auth_entry.sc.chain_id, decode_unsigned<uint256_t>(payload));

    BOOST_OUTCOME_TRY(auth_entry.address, decode_address(payload));
    BOOST_OUTCOME_TRY(auth_entry.nonce, decode_unsigned<uint64_t>(payload));

    BOOST_OUTCOME_TRY(
        auth_entry.sc.signature.y_parity, decode_unsigned<uint8_t>(payload));
    BOOST_OUTCOME_TRY(
        auth_entry.sc.signature.r, decode_unsigned<uint256_t>(payload));
    BOOST_OUTCOME_TRY(
        auth_entry.sc.signature.s, decode_unsigned<uint256_t>(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return auth_entry;
}

Result<AuthorizationList> decode_authorization_list(byte_string_view &enc)
{
    AuthorizationList auth_list;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    auto const list_space = payload.size();
    auth_list.reserve(list_space / sizeof(AuthorizationEntry));

    while (payload.size() > 0) {
        BOOST_OUTCOME_TRY(auto auth_entry, decode_authorization_entry(payload));
        auth_list.emplace_back(std::move(auth_entry));
    }
    MONAD_ASSERT(payload.empty());

    return auth_list;
}

Result<Transaction> decode_transaction_legacy(byte_string_view &enc)
{
    Transaction txn;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    txn.type = TransactionType::legacy;
    BOOST_OUTCOME_TRY(txn.nonce, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(txn.max_fee_per_gas, decode_unsigned<uint256_t>(payload));
    BOOST_OUTCOME_TRY(txn.gas_limit, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(txn.to, decode_optional_address(payload));
    BOOST_OUTCOME_TRY(txn.value, decode_unsigned<uint256_t>(payload));
    BOOST_OUTCOME_TRY(txn.data, decode_string(payload));
    BOOST_OUTCOME_TRY(txn.sc, decode_sc(payload));
    BOOST_OUTCOME_TRY(txn.sc.signature.r, decode_unsigned<uint256_t>(payload));
    BOOST_OUTCOME_TRY(txn.sc.signature.s, decode_unsigned<uint256_t>(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return txn;
}

namespace
{
    Result<std::pair<uint8_t, byte_string_view>>
    decode_feature(byte_string_view &features, uint8_t &previous)
    {
        BOOST_OUTCOME_TRY(auto pair, parse_list_metadata(features));
        BOOST_OUTCOME_TRY(auto const key, parse_string_metadata(pair));
        if (key.size() != 1 || key[0] <= previous) {
            return DecodeError::NonCanonical;
        }
        previous = key[0];
        return std::pair{previous, pair};
    }

    Result<Transaction> decode_monad_transaction(byte_string_view &enc)
    {
        Transaction txn;
        txn.type = TransactionType::monad;
        BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));
        BOOST_OUTCOME_TRY(
            auto const chain_id, decode_unsigned<uint256_t>(payload));
        txn.sc.chain_id = chain_id;
        BOOST_OUTCOME_TRY(auto features, parse_list_metadata(payload));
        // Auxiliary data belongs only to the RPC submission wrapper.
        if (!payload.empty() || !enc.empty()) {
            return DecodeError::InputTooLong;
        }
        uint8_t previous = 0;
        uint8_t present = 0;
        while (!features.empty()) {
            BOOST_OUTCOME_TRY(auto pair, decode_feature(features, previous));
            auto &[key, value] = pair;
            switch (key) {
            case 1: {
                BOOST_OUTCOME_TRY(txn.nonce, decode_unsigned<uint64_t>(value));
                break;
            }
            case 2: {
                BOOST_OUTCOME_TRY(
                    txn.gas_limit, decode_unsigned<uint64_t>(value));
                break;
            }
            case 3: {
                BOOST_OUTCOME_TRY(auto call, parse_list_metadata(value));
                uint8_t call_previous = 0;
                for (uint8_t expected = 1; expected <= 3; ++expected) {
                    BOOST_OUTCOME_TRY(
                        auto call_pair, decode_feature(call, call_previous));
                    auto &[call_key, field] = call_pair;
                    if (call_key != expected) {
                        return DecodeError::NonCanonical;
                    }
                    if (call_key == 1) {
                        BOOST_OUTCOME_TRY(
                            txn.to, decode_optional_address(field));
                    }
                    else if (call_key == 2) {
                        BOOST_OUTCOME_TRY(
                            txn.value, decode_unsigned<uint256_t>(field));
                    }
                    else {
                        BOOST_OUTCOME_TRY(txn.data, decode_string(field));
                    }
                    if (!field.empty()) {
                        return DecodeError::InputTooLong;
                    }
                }
                if (!call.empty()) {
                    return DecodeError::InputTooLong;
                }
                break;
            }
            case 4: {
                txn.monad_access_list_present = true;
                BOOST_OUTCOME_TRY(txn.access_list, decode_access_list(value));
                break;
            }
            case 6: {
                BOOST_OUTCOME_TRY(auto sig, parse_list_metadata(value));
                BOOST_OUTCOME_TRY(
                    txn.sc.signature.y_parity, decode_unsigned<uint8_t>(sig));
                BOOST_OUTCOME_TRY(
                    txn.sc.signature.r, decode_unsigned<uint256_t>(sig));
                BOOST_OUTCOME_TRY(
                    txn.sc.signature.s, decode_unsigned<uint256_t>(sig));
                if (!sig.empty() || txn.sc.signature.y_parity > 1) {
                    return DecodeError::NonCanonical;
                }
                break;
            }
            case 7: {
                BOOST_OUTCOME_TRY(auto fees, parse_list_metadata(value));
                BOOST_OUTCOME_TRY(
                    txn.max_priority_fee_per_gas,
                    decode_unsigned<uint256_t>(fees));
                BOOST_OUTCOME_TRY(
                    txn.max_fee_per_gas, decode_unsigned<uint256_t>(fees));
                if (!fees.empty()) {
                    return DecodeError::InputTooLong;
                }
                break;
            }
            default:
                return DecodeError::InvalidTxnType;
            }
            present |= static_cast<uint8_t>(1u << key);
            if (!value.empty()) {
                return DecodeError::InputTooLong;
            }
        }
        if ((present & 0xce) != 0xce) {
            return DecodeError::InputTooShort;
        }
        return txn;
    }
}

Result<Transaction> decode_transaction_eip2718(byte_string_view &enc)
{
    Transaction txn;
    if (MONAD_UNLIKELY(enc.empty())) {
        return DecodeError::InputTooShort;
    }
    if (enc[0] == 0x40) {
        enc = enc.substr(1);
        return decode_monad_transaction(enc);
    }
    if (MONAD_UNLIKELY(
            enc[0] >= static_cast<unsigned char>(TransactionType::LAST))) {
        return DecodeError::InvalidTxnType;
    }
    txn.type = static_cast<TransactionType>(enc[0]);
    enc = enc.substr(1);
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    txn.sc.chain_id = uint256_t{};
    BOOST_OUTCOME_TRY(*txn.sc.chain_id, decode_unsigned<uint256_t>(payload));
    BOOST_OUTCOME_TRY(txn.nonce, decode_unsigned<uint64_t>(payload));

    if (txn.type == TransactionType::eip1559 ||
        txn.type == TransactionType::eip4844 ||
        txn.type == TransactionType::eip7702) {
        BOOST_OUTCOME_TRY(
            txn.max_priority_fee_per_gas, decode_unsigned<uint256_t>(payload));
    }

    BOOST_OUTCOME_TRY(txn.max_fee_per_gas, decode_unsigned<uint256_t>(payload));
    BOOST_OUTCOME_TRY(txn.gas_limit, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(txn.to, decode_optional_address(payload));
    BOOST_OUTCOME_TRY(txn.value, decode_unsigned<uint256_t>(payload));
    BOOST_OUTCOME_TRY(txn.data, decode_string(payload));
    BOOST_OUTCOME_TRY(txn.access_list, decode_access_list(payload));

    if (txn.type == TransactionType::eip4844) {
        if (!txn.to.has_value()) {
            return DecodeError::InputTooShort;
        }
        BOOST_OUTCOME_TRY(
            txn.max_fee_per_blob_gas, decode_unsigned<uint256_t>(payload));
        BOOST_OUTCOME_TRY(auto hashes_payload, parse_list_metadata(payload));
        while (!hashes_payload.empty()) {
            BOOST_OUTCOME_TRY(auto const hash, decode_bytes32(hashes_payload));
            txn.blob_versioned_hashes.emplace_back(std::move(hash));
        }
    }

    if (txn.type == TransactionType::eip7702) {
        if (!txn.to.has_value()) {
            return DecodeError::InputTooShort;
        }

        BOOST_OUTCOME_TRY(
            txn.authorization_list, decode_authorization_list(payload));
    }

    BOOST_OUTCOME_TRY(
        txn.sc.signature.y_parity, decode_unsigned<uint8_t>(payload));
    BOOST_OUTCOME_TRY(txn.sc.signature.r, decode_unsigned<uint256_t>(payload));
    BOOST_OUTCOME_TRY(txn.sc.signature.s, decode_unsigned<uint256_t>(payload));

    if (MONAD_UNLIKELY(!payload.empty() || !enc.empty())) {
        return DecodeError::InputTooLong;
    }

    return txn;
}

Result<Transaction> decode_transaction(byte_string_view &enc)
{
    if (MONAD_UNLIKELY(enc.empty())) {
        return DecodeError::InputTooShort;
    }

    if (enc[0] >= 0xc0) {
        return decode_transaction_legacy(enc);
    }
    else {
        return decode_transaction_eip2718(enc);
    }
}

template <NullptrOrRef<std::vector<byte_string_view>> Out>
Result<std::vector<Transaction>>
decode_transaction_list(byte_string_view &enc, Out const raw_transactions)
{
    constexpr bool keep_raw_transactions = !std::same_as<Out, std::nullptr_t>;

    std::vector<Transaction> transactions;
    BOOST_OUTCOME_TRY(auto ls, parse_list_metadata(enc));

    // TODO: Reserve txn vector size for better perf
    while (!ls.empty()) {
        if (ls[0] >= 0xc0) {
            auto const before = ls;
            BOOST_OUTCOME_TRY(auto tx, decode_transaction_legacy(ls));
            if constexpr (keep_raw_transactions) {
                raw_transactions.get().push_back(
                    before.substr(0, before.size() - ls.size()));
            }
            transactions.emplace_back(std::move(tx));
        }
        else {
            BOOST_OUTCOME_TRY(auto str, parse_string_metadata(ls));
            // raw_transactions entries must be parsable with
            // decode_transaction, hence we store the unwrapped str payload
            if constexpr (keep_raw_transactions) {
                raw_transactions.get().push_back(str);
            }
            BOOST_OUTCOME_TRY(auto tx, decode_transaction_eip2718(str));
            transactions.emplace_back(std::move(tx));
        }
    }
    MONAD_ASSERT(ls.empty());

    return transactions;
}

template Result<std::vector<Transaction>>
decode_transaction_list<std::nullptr_t>(byte_string_view &, std::nullptr_t);
template Result<std::vector<Transaction>>
decode_transaction_list<std::reference_wrapper<std::vector<byte_string_view>>>(
    byte_string_view &, std::reference_wrapper<std::vector<byte_string_view>>);

MONAD_RLP_NAMESPACE_END
