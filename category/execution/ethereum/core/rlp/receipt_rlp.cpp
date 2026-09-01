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
#include <category/core/address.hpp>
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
#include <cstring>
#include <cstdint>
#include <utility>
#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

// Encode

namespace
{
    // Significant byte count of `size`, i.e. the length to_big_compact gives
    // it. Only ever called with size > 55, so it is never zero.
    size_t compact_len(size_t size)
    {
        size_t n = 0;
        while (size != 0) {
            ++n;
            size >>= 8;
        }
        return n;
    }

    size_t list_header_len(size_t const size)
    {
        return size > 55 ? 1 + compact_len(size) : 1;
    }

    void append_length(unsigned char *&p, unsigned char const base,
        size_t const size)
    {
        size_t const n = compact_len(size);
        *p++ = static_cast<unsigned char>(base + n);
        for (size_t i = n; i-- > 0;) {
            *p++ = static_cast<unsigned char>(size >> (i * 8));
        }
    }

    // encode_list2's header, written into an existing buffer instead of at
    // the front of a fresh one.
    void append_list_header(unsigned char *&p, size_t const size)
    {
        if (MONAD_LIKELY(size <= 55)) {
            *p++ = static_cast<unsigned char>(0xc0 + size);
            return;
        }
        append_length(p, 0xf7, size);
    }

    size_t string_len(byte_string_view const s)
    {
        if (s.size() == 1 && s[0] <= 0x7f) {
            return 1;
        }
        return (s.size() > 55 ? 1 + compact_len(s.size()) : 1) + s.size();
    }

    // encode_string2, appended rather than returned.
    void append_string(unsigned char *&p, byte_string_view const s)
    {
        if (s.size() == 1 && s[0] <= 0x7f) {
            *p++ = s[0];
            return;
        }
        if (MONAD_LIKELY(s.size() <= 55)) {
            *p++ = static_cast<unsigned char>(0x80 + s.size());
        }
        else {
            append_length(p, 0xb7, s.size());
        }
        std::memcpy(p, s.data(), s.size());
        p += s.size();
    }

    size_t log_payload_len(Receipt::Log const &log)
    {
        size_t const topics_payload =
            log.topics.size() * (1 + sizeof(bytes32_t));
        return (1 + sizeof(Address)) + list_header_len(topics_payload) +
            topics_payload + string_len(log.data);
    }

    size_t log_len(Receipt::Log const &log)
    {
        size_t const payload = log_payload_len(log);
        return list_header_len(payload) + payload;
    }

    // A log, appended in place. The nested encoding is written directly into
    // the caller's buffer: every length below is known before a byte is
    // emitted, so no part of it has to be built in a temporary first.
    //
    // An address is always 20 bytes and a topic always 32, so both headers are
    // constants -- 0x80 + 20 and 0x80 + 32 -- never in the long form and never
    // in the single-byte form.
    void append_log(unsigned char *&p, Receipt::Log const &log)
    {
        static_assert(sizeof(bytes32_t) == 32);
        static_assert(sizeof(Address) == 20);
        constexpr unsigned char address_header = 0x80 + sizeof(Address);
        constexpr unsigned char topic_header = 0x80 + sizeof(bytes32_t);

        size_t const topics_payload =
            log.topics.size() * (1 + sizeof(bytes32_t));

        append_list_header(p, log_payload_len(log));
        *p++ = address_header;
        std::memcpy(p, log.address.bytes, sizeof(log.address.bytes));
        p += sizeof(log.address.bytes);
        append_list_header(p, topics_payload);
        for (auto const &i : log.topics) {
            *p++ = topic_header;
            std::memcpy(p, i.bytes, sizeof(i.bytes));
            p += sizeof(i.bytes);
        }
        append_string(p, log.data);
    }
}

byte_string encode_topics(std::vector<bytes32_t> const &topics)
{
    static_assert(sizeof(bytes32_t) == 32);
    constexpr unsigned char topic_header = 0x80 + sizeof(bytes32_t);

    byte_string result{};
    result.reserve(topics.size() * (1 + sizeof(bytes32_t)));
    for (auto const &i : topics) {
        result.push_back(topic_header);
        result.append(i.bytes, sizeof(i.bytes));
    }
    return encode_list2(result);
}

byte_string encode_log(Receipt::Log const &log)
{
    byte_string result{};
    result.resize_and_overwrite(
        log_len(log), [&log](unsigned char *const buf, size_t const n) {
            unsigned char *p = buf;
            append_log(p, log);
            MONAD_ASSERT(p == buf + n);
            return n;
        });
    return result;
}

byte_string encode_bloom(Receipt::Bloom const &bloom)
{
    return encode_string2(to_byte_string_view(bloom));
}

byte_string encode_receipt(Receipt const &receipt)
{
    // Assembled in a single buffer. The logs are the bulk of a receipt, and
    // composing this through encode_list2 copies them end to end three times
    // over -- once to close the log list, once into the receipt's own list,
    // and once more to put the type byte in front -- each copy through a
    // fresh allocation, because encode_list2 takes its arguments by reference
    // and so cannot write a header ahead of a payload it does not own. Every
    // length here is known before a byte is emitted, so the type byte and
    // both headers go down first and every log byte is written exactly once.
    size_t logs_payload = 0;
    for (auto const &i : receipt.logs) {
        logs_payload += log_len(i);
    }

    auto const status = encode_unsigned(receipt.status);
    auto const gas_used = encode_unsigned(receipt.gas_used);
    auto const bloom = encode_bloom(receipt.bloom);

    size_t const payload = status.size() + gas_used.size() + bloom.size() +
        list_header_len(logs_payload) + logs_payload;

    bool const typed = receipt.type == TransactionType::eip1559 ||
        receipt.type == TransactionType::eip2930 ||
        receipt.type == TransactionType::eip4844 ||
        receipt.type == TransactionType::eip7702;

    // Sized once and written through a cursor. Every length above is exact,
    // so there is no capacity test and no size store per byte -- and
    // resize_and_overwrite rather than resize, because resize would zero every
    // byte first and each one is about to be written anyway.
    //
    // The assert is what keeps the arithmetic honest: land anywhere but the
    // end and the block fails here rather than at the receipts root.
    byte_string result{};
    result.resize_and_overwrite(
        static_cast<size_t>(typed) + list_header_len(payload) + payload,
        [&](unsigned char *const buf, size_t const n) {
            unsigned char *p = buf;
            if (typed) {
                *p++ = static_cast<unsigned char>(receipt.type);
            }
            append_list_header(p, payload);
            auto const put = [&p](byte_string const &b) {
                std::memcpy(p, b.data(), b.size());
                p += b.size();
            };
            put(status);
            put(gas_used);
            put(bloom);
            append_list_header(p, logs_payload);
            for (auto const &i : receipt.logs) {
                append_log(p, i);
            }
            MONAD_ASSERT(p == buf + n);
            return n;
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
        BOOST_OUTCOME_TRY(auto topic, decode_bytes32(payload));
        topics.emplace_back(std::move(topic));
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
