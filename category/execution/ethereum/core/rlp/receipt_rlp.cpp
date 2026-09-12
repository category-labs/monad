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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <category/core/rlp/decode_error.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/address_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/receipt_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <utility>
#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

// Encode

namespace
{
    size_t log_payload_size(Receipt::Log const &log)
    {
        size_t const topics_payload =
            log.topics.size() * (1 + sizeof(bytes32_t));
        return (1 + sizeof(Address)) + list_header_size(topics_payload) +
               topics_payload + encoded_string_size(log.data);
    }

    size_t encoded_log_size(Receipt::Log const &log)
    {
        size_t const payload = log_payload_size(log);
        return list_header_size(payload) + payload;
    }

    // Write directly into the pre-sized buffer. Address and topic headers
    // have fixed one-byte encodings for their 20- and 32-byte payloads.
    void append_log(unsigned char *&cursor, Receipt::Log const &log)
    {
        static_assert(sizeof(bytes32_t) == 32);
        static_assert(sizeof(Address) == 20);
        constexpr unsigned char address_header = 0x80 + sizeof(Address);
        constexpr unsigned char topic_header = 0x80 + sizeof(bytes32_t);

        size_t const topics_payload =
            log.topics.size() * (1 + sizeof(bytes32_t));

        append_list_header(cursor, log_payload_size(log));
        *cursor++ = static_cast<unsigned char>(address_header);
        std::memcpy(cursor, log.address.bytes, sizeof(log.address.bytes));
        cursor += sizeof(log.address.bytes);
        append_list_header(cursor, topics_payload);
        for (auto const &i : log.topics) {
            *cursor++ = static_cast<unsigned char>(topic_header);
            std::memcpy(cursor, i.bytes, sizeof(i.bytes));
            cursor += sizeof(i.bytes);
        }
        append_string2(cursor, log.data);
    }
}

byte_string encode_log(Receipt::Log const &log)
{
    byte_string result{};
    result.resize_and_overwrite(
        encoded_log_size(log),
        [&log](unsigned char *const buffer, size_t const buffer_size) {
            unsigned char *cursor = buffer;
            append_log(cursor, log);
            MONAD_ASSERT(cursor == buffer + buffer_size);
            return buffer_size;
        });
    return result;
}

byte_string encode_bloom(Receipt::Bloom const &bloom)
{
    return encode_string2(to_byte_string_view(bloom));
}

byte_string encode_receipt(Receipt const &receipt)
{
    // Size all nested lists before allocating, then write each log once.
    size_t logs_payload = 0;
    for (auto const &i : receipt.logs) {
        logs_payload += encoded_log_size(i);
    }

    // Small integer encodings stay inline; append the bloom without a copy.
    auto const status = encode_unsigned(receipt.status);
    auto const gas_used = encode_unsigned(receipt.gas_used);
    auto const bloom = to_byte_string_view(receipt.bloom);

    size_t const payload = status.size() + gas_used.size() +
                           encoded_string_size(bloom) +
                           list_header_size(logs_payload) + logs_payload;

    bool const typed = receipt.type == TransactionType::eip1559 ||
                       receipt.type == TransactionType::eip2930 ||
                       receipt.type == TransactionType::eip4844 ||
                       receipt.type == TransactionType::eip7702;

    // Every byte is overwritten, so avoid resize()'s initial zero-fill.
    // Unchecked writes rely on exact sizes; the final assert checks the cursor.
    byte_string result{};
    result.resize_and_overwrite(
        static_cast<size_t>(typed) + list_header_size(payload) + payload,
        [&](unsigned char *const buffer, size_t const buffer_size) {
            unsigned char *cursor = buffer;
            if (typed) {
                *cursor++ = static_cast<unsigned char>(receipt.type);
            }
            append_list_header(cursor, payload);
            auto const append_encoded = [&cursor](
                                            byte_string const &encoded_bytes) {
                // Encoded RLP, not a string: nothing to NUL-terminate.
                // NOLINTNEXTLINE(bugprone-not-null-terminated-result)
                std::memcpy(cursor, encoded_bytes.data(), encoded_bytes.size());
                cursor += encoded_bytes.size();
            };
            append_encoded(status);
            append_encoded(gas_used);
            append_string2(cursor, bloom);
            append_list_header(cursor, logs_payload);
            for (auto const &i : receipt.logs) {
                append_log(cursor, i);
            }
            MONAD_ASSERT(cursor == buffer + buffer_size);
            return buffer_size;
        });
    return result;
}

// Decode
Result<Receipt::Bloom> decode_bloom(byte_string_view &enc)
{
    return decode_byte_string_fixed<256>(enc);
}

Result<std::vector<bytes32_t>> decode_topics(byte_string_view &enc)
{
    std::vector<bytes32_t> topics;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));
    constexpr size_t topic_size =
        33; // 1 byte for header, 32 bytes for byte32_t
    auto const list_space = payload.size();
    topics.reserve(list_space / topic_size);

    while (payload.size() > 0) {
        BOOST_OUTCOME_TRY(auto const topic, decode_bytes32(payload));
        topics.emplace_back(topic);
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return topics;
}

Result<Receipt::Log> decode_log(byte_string_view &enc)
{
    Receipt::Log log;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));
    BOOST_OUTCOME_TRY(log.address, decode_address(payload));
    BOOST_OUTCOME_TRY(log.topics, decode_topics(payload));
    BOOST_OUTCOME_TRY(log.data, decode_string(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return log;
}

Result<std::vector<Receipt::Log>> decode_logs(byte_string_view &enc)
{
    std::vector<Receipt::Log> logs;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    while (payload.size() > 0) {
        BOOST_OUTCOME_TRY(auto log, decode_log(payload));
        logs.emplace_back(std::move(log));
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return logs;
}

Result<Receipt> decode_untyped_receipt(byte_string_view &enc)
{
    Receipt receipt;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));
    BOOST_OUTCOME_TRY(receipt.status, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(receipt.gas_used, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(receipt.bloom, decode_bloom(payload));
    BOOST_OUTCOME_TRY(receipt.logs, decode_logs(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return receipt;
}

Result<Receipt> decode_receipt(byte_string_view &enc)
{
    if (MONAD_UNLIKELY(enc.empty())) {
        return DecodeError::InputTooShort;
    }

    Receipt receipt;

    unsigned char const first = enc[0];
    if (first < 0xc0) // eip 2718 - typed transaction envelope
    {
        enc = enc.substr(1);
        BOOST_OUTCOME_TRY(receipt, decode_untyped_receipt(enc));
        switch (first) {
        case 0x1:
            receipt.type = TransactionType::eip2930;
            break;
        case 0x2:
            receipt.type = TransactionType::eip1559;
            break;
        case 0x3:
            receipt.type = TransactionType::eip4844;
            break;
        case 0x4:
            receipt.type = TransactionType::eip7702;
            break;
        default:
            return DecodeError::InvalidTxnType;
        }

        return receipt;
    }
    else {
        BOOST_OUTCOME_TRY(receipt, decode_untyped_receipt(enc));
        receipt.type = TransactionType::legacy;

        return receipt;
    }
}

MONAD_RLP_NAMESPACE_END
