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
#include <category/execution/ethereum/core/rlp/address_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/signature_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/signature.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/decode_error.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

#include <cassert>
#include <cstddef>
#include <cstdint>
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
        txn.type == TransactionType::eip4844) {
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
        auto const prefix =
            byte_string(1, static_cast<unsigned char>(txn.type));

        return prefix + encode_list2(
                            encode_eip2718_base(txn),
                            encode_unsigned(txn.sc.y_parity),
                            encode_unsigned(txn.sc.r),
                            encode_unsigned(txn.sc.s));
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
    BOOST_OUTCOME_TRY(txn.sc.r, decode_unsigned<uint256_t>(payload));
    BOOST_OUTCOME_TRY(txn.sc.s, decode_unsigned<uint256_t>(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return txn;
}

Result<Transaction> decode_transaction_eip2718(byte_string_view &enc)
{
    Transaction txn;
    MONAD_ASSERT(enc.size());
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
        txn.type == TransactionType::eip4844) {
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
        while (hashes_payload.size() >= sizeof(bytes32_t)) {
            BOOST_OUTCOME_TRY(auto const hash, decode_bytes32(hashes_payload));
            txn.blob_versioned_hashes.emplace_back(std::move(hash));
        }
    }

    BOOST_OUTCOME_TRY(txn.sc.y_parity, decode_unsigned<uint8_t>(payload));
    BOOST_OUTCOME_TRY(txn.sc.r, decode_unsigned<uint256_t>(payload));
    BOOST_OUTCOME_TRY(txn.sc.s, decode_unsigned<uint256_t>(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
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

Result<std::vector<Transaction>> decode_transaction_list(byte_string_view &enc)
{
    std::vector<Transaction> transactions;
    BOOST_OUTCOME_TRY(auto ls, parse_list_metadata(enc));

    // TODO: Reserve txn vector size for better perf
    while (!ls.empty()) {
        if (ls[0] >= 0xc0) {
            BOOST_OUTCOME_TRY(auto tx, decode_transaction_legacy(ls));
            transactions.emplace_back(std::move(tx));
        }
        else {
            BOOST_OUTCOME_TRY(auto str, parse_string_metadata(ls));
            BOOST_OUTCOME_TRY(auto tx, decode_transaction_eip2718(str));
            transactions.emplace_back(std::move(tx));
        }
    }
    MONAD_ASSERT(ls.empty());

    return transactions;
}

MONAD_RLP_NAMESPACE_END
