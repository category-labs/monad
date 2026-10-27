// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/execution/monad/private_domain_scanner.hpp>

#include <category/core/hex.hpp>
#include <category/execution/ethereum/core/contract/abi_decode_error.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/contract/events.hpp>

#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <optional>
#include <span>
#include <vector>

using namespace monad;
using namespace monad::literals;

namespace
{
    constexpr uint64_t NETWORK_CHAIN_ID = 20143;
    constexpr uint64_t DOMAIN = 0x114eaf;
    constexpr uint64_t OTHER_DOMAIN = 0x124eaf;
    constexpr Address HUB = 0x1234567890abcdef1234567890abcdef12345678_address;
    constexpr Address FEE_RECIPIENT =
        0x3333333333333333333333333333333333333333_address;
    constexpr Address MESSAGE_FROM =
        0x1111111111111111111111111111111111111111_address;
    constexpr Address MESSAGE_TO =
        0x2222222222222222222222222222222222222222_address;
    constexpr std::array<uint64_t, 1> DOMAINS{DOMAIN};

    Receipt::Log make_registered(uint64_t const domain = DOMAIN)
    {
        return EventBuilder(
                   HUB,
                   abi_encode_event_signature(
                       "DomainRegistered(uint64,address,uint64)"))
            .add_topic(abi_encode_uint(u64_be{domain}))
            .add_topic(abi_encode_address(FEE_RECIPIENT))
            .add_data(abi_encode_uint(u64_be{100}))
            .build();
    }

    Receipt::Log make_sequenced(
        byte_string_view const payload, uint64_t const domain = DOMAIN)
    {
        // Non-indexed `(bytes rlpTx, uint256 fee)`.
        byte_string encoded;
        encoded += abi_encode_uint(u256_be{2 * 32});
        encoded += abi_encode_uint(u256_be{5});
        encoded += abi_encode_bytes(payload);
        return EventBuilder(
                   HUB,
                   abi_encode_event_signature(
                       "DomainTransactionSequenced(uint64,bytes,uint256)"))
            .add_topic(abi_encode_uint(u64_be{domain}))
            .add_data(encoded)
            .build();
    }

    Receipt::Log make_message(
        byte_string_view const data, uint64_t const nonce,
        uint64_t const domain = DOMAIN,
        uint64_t const source_chain_id = NETWORK_CHAIN_ID)
    {
        // Non-indexed `(uint64 sourceChainId, bytes data, uint256 nonce,
        // uint256 fee, bytes32 messageHash)`.
        byte_string encoded;
        encoded += abi_encode_uint(u64_be{source_chain_id});
        encoded += abi_encode_uint(u256_be{5 * 32});
        encoded += abi_encode_uint(u256_be{nonce});
        encoded += abi_encode_uint(u256_be{9});
        encoded += bytes32_t{0xab};
        encoded += abi_encode_bytes(data);
        return EventBuilder(
                   HUB,
                   abi_encode_event_signature(
                       "L1MessageRecorded(uint64,uint64,address,address,bytes,"
                       "uint256,uint256,bytes32)"))
            .add_topic(abi_encode_uint(u64_be{domain}))
            .add_topic(abi_encode_address(MESSAGE_FROM))
            .add_topic(abi_encode_address(MESSAGE_TO))
            .add_data(encoded)
            .build();
    }

    Receipt receipt_with(std::vector<Receipt::Log> const &logs)
    {
        Receipt receipt;
        for (auto const &log : logs) {
            receipt.add_log(log);
        }
        return receipt;
    }

    Result<DomainHubEvents> scan(std::span<Receipt const> const receipts)
    {
        return scan_domain_hub_events(receipts, HUB, DOMAINS);
    }
}

TEST(PrivateDomainScanner, extracts_solidity_reference_sequenced_payload)
{
    // `cast abi-encode "f(bytes,uint256)" 0xdeadbeef 5`.
    auto log = make_sequenced({});
    log.data = *from_hex(
        "0000000000000000000000000000000000000000000000000000000000000040"
        "0000000000000000000000000000000000000000000000000000000000000005"
        "0000000000000000000000000000000000000000000000000000000000000004"
        "deadbeef00000000000000000000000000000000000000000000000000000000");
    std::array const receipts{Receipt{}, receipt_with({log})};

    auto const result = scan(receipts);

    ASSERT_TRUE(result.has_value());
    ASSERT_EQ(result.value().sequenced.size(), 1);
    EXPECT_EQ(
        result.value().sequenced[0],
        (SequencedDomainPayload{
            .domain_chain_id = DOMAIN,
            .l1_transaction_index = 1,
            .payload = byte_string{0xde, 0xad, 0xbe, 0xef},
            .fee = 5}));
    EXPECT_TRUE(result.value().registered_domains.empty());
    EXPECT_TRUE(result.value().messages.empty());
}

TEST(PrivateDomainScanner, extracts_registration)
{
    std::array const receipts{receipt_with({make_registered()})};

    auto const result = scan(receipts);

    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result.value().registered_domains, std::vector<uint64_t>{DOMAIN});
}

TEST(PrivateDomainScanner, extracts_solidity_reference_l1_message)
{
    // `cast abi-encode "f(uint64,bytes,uint256,uint256,bytes32)" 20143
    //  0xdeadbeef 7 9 0xab..ab`.
    auto log = make_message({}, 0);
    log.data = *from_hex(
        "0000000000000000000000000000000000000000000000000000000000004eaf"
        "00000000000000000000000000000000000000000000000000000000000000a0"
        "0000000000000000000000000000000000000000000000000000000000000007"
        "0000000000000000000000000000000000000000000000000000000000000009"
        "abababababababababababababababababababababababababababababababab"
        "0000000000000000000000000000000000000000000000000000000000000004"
        "deadbeef00000000000000000000000000000000000000000000000000000000");
    std::array const receipts{receipt_with({log})};

    auto const result = scan(receipts);

    ASSERT_TRUE(result.has_value());
    ASSERT_EQ(result.value().messages.size(), 1);
    EXPECT_EQ(
        result.value().messages[0],
        (L1DomainMessage{
            .domain_chain_id = DOMAIN,
            .source_chain_id = NETWORK_CHAIN_ID,
            .from = MESSAGE_FROM,
            .to = MESSAGE_TO,
            .data = byte_string{0xde, 0xad, 0xbe, 0xef},
            .nonce = 7,
            .fee = 9,
            .l1_transaction_index = 0}));
}

TEST(PrivateDomainScanner, ignores_encrypted_l1_messages)
{
    // The protocol derives no EncryptedL1MessageRecorded event.
    byte_string encoded;
    encoded += abi_encode_uint(u64_be{NETWORK_CHAIN_ID});
    encoded += abi_encode_uint(u256_be{4 * 32});
    encoded += abi_encode_uint(u256_be{0});
    encoded += abi_encode_uint(u256_be{9});
    encoded += abi_encode_bytes(byte_string{1, 2, 3});
    auto const log = EventBuilder(
                         HUB,
                         abi_encode_event_signature(
                             "EncryptedL1MessageRecorded(uint64,uint64,address,"
                             "bytes,uint256,uint256)"))
                         .add_topic(abi_encode_uint(u64_be{DOMAIN}))
                         .add_topic(abi_encode_address(MESSAGE_FROM))
                         .add_data(encoded)
                         .build();
    std::array const receipts{receipt_with({log})};

    auto const result = scan(receipts);

    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result.value(), DomainHubEvents{});
}

TEST(PrivateDomainScanner, keeps_receipt_and_log_order_per_kind)
{
    std::array const receipts{
        receipt_with(
            {make_sequenced(byte_string{1}),
             make_message(byte_string{0xa}, 0),
             make_sequenced(byte_string{2})}),
        receipt_with(
            {make_message(byte_string{0xb}, 1),
             make_sequenced(byte_string{3})})};

    auto const result = scan(receipts);

    ASSERT_TRUE(result.has_value());
    auto const &events = result.value();
    ASSERT_EQ(events.sequenced.size(), 3);
    EXPECT_EQ(events.sequenced[0].payload, byte_string{1});
    EXPECT_EQ(events.sequenced[1].payload, byte_string{2});
    EXPECT_EQ(events.sequenced[2].payload, byte_string{3});
    EXPECT_EQ(events.sequenced[2].l1_transaction_index, 1);
    ASSERT_EQ(events.messages.size(), 2);
    EXPECT_EQ(events.messages[0].nonce, 0);
    EXPECT_EQ(events.messages[0].data, byte_string{0xa});
    EXPECT_EQ(events.messages[1].nonce, 1);
    EXPECT_EQ(events.messages[1].l1_transaction_index, 1);
}

TEST(PrivateDomainScanner, accepts_payload_sizes_across_words)
{
    for (size_t const size : {0uz, 1uz, 31uz, 32uz, 33uz, 64uz, 65uz}) {
        byte_string const payload(size, 0x5a);
        std::array const receipts{receipt_with({make_sequenced(payload)})};

        auto const result = scan(receipts);

        ASSERT_TRUE(result.has_value()) << size;
        ASSERT_EQ(result.value().sequenced.size(), 1) << size;
        EXPECT_EQ(result.value().sequenced[0].payload, payload) << size;
    }
}

TEST(PrivateDomainScanner, receipt_bloom_skips_log_scan)
{
    auto receipt = receipt_with({make_sequenced(byte_string{1})});
    receipt.bloom = {};
    std::array const receipts{receipt};

    auto const result = scan(receipts);

    ASSERT_TRUE(result.has_value());
    EXPECT_TRUE(result.value().sequenced.empty());
}

TEST(PrivateDomainScanner, filters_emitter_and_unconfigured_domain)
{
    auto wrong_emitter = make_sequenced(byte_string{1});
    wrong_emitter.address = Address{1};
    // Malformed, but for a domain this node does not serve.
    auto unconfigured = make_sequenced(byte_string{2}, OTHER_DOMAIN);
    unconfigured.data.pop_back();
    std::array const receipts{receipt_with(
        {wrong_emitter, unconfigured, make_registered(OTHER_DOMAIN)})};

    auto const result = scan(receipts);

    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result.value(), DomainHubEvents{});

    auto const none =
        scan_domain_hub_events(receipts, HUB, std::span<uint64_t const>{});
    ASSERT_TRUE(none.has_value());
    EXPECT_EQ(none.value(), DomainHubEvents{});
}

TEST(PrivateDomainScanner, rejects_malformed_events_of_served_domain)
{
    auto truncated = make_sequenced(byte_string{1, 2, 3});
    truncated.data.pop_back();

    auto trailing = make_sequenced(byte_string{1, 2, 3});
    trailing.data += bytes32_t{};

    auto bad_offset = make_sequenced(byte_string{1, 2, 3});
    bad_offset.data[31] = 0x60;

    auto dirty_padding = make_sequenced(byte_string{1, 2, 3});
    dirty_padding.data.back() = 1;

    auto missing_topic = make_message(byte_string{1}, 0);
    missing_topic.topics.pop_back();

    auto registered_extra_data = make_registered();
    registered_extra_data.data += bytes32_t{};

    for (auto const &log :
         {truncated,
          trailing,
          bad_offset,
          dirty_padding,
          missing_topic,
          registered_extra_data}) {
        std::array const receipts{receipt_with({log})};
        EXPECT_TRUE(scan(receipts).has_error());
    }
}
