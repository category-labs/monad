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

#include <category/execution/domain/scan_domain_inputs.hpp>

#include <category/core/hex.hpp>
#include <category/execution/domain/inputs.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/contract/abi_decode_error.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/contract/events.hpp>

#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <optional>
#include <span>
#include <utility>
#include <variant>
#include <vector>

using namespace monad;
using namespace monad::domain;
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
    constexpr uint64_t L1_BLOCK_NUMBER = 77;
    constexpr uint64_t L1_TIMESTAMP = 1'700'000'000;
    constexpr bytes32_t L1_PREV_RANDAO{0x5a};
    constexpr uint64_t L1_SLOT_NUMBER = 91;

    BlockHeader l1_header()
    {
        return BlockHeader{
            .prev_randao = L1_PREV_RANDAO,
            .number = L1_BLOCK_NUMBER,
            .timestamp = L1_TIMESTAMP,
            .slot_number = L1_SLOT_NUMBER};
    }

    // The inputs of a block of l1_header() that holds `inputs`.
    DomainInputs inputs_of(std::vector<DomainInput> inputs)
    {
        return DomainInputs{
            .l1_block_number = L1_BLOCK_NUMBER,
            .timestamp = L1_TIMESTAMP,
            .prev_randao = L1_PREV_RANDAO,
            .slot_number = L1_SLOT_NUMBER,
            .inputs = std::move(inputs)};
    }

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

    Receipt::Log make_encrypted_message(byte_string_view const ciphertext)
    {
        // Non-indexed `(uint64 sourceChainId, bytes ciphertext, uint256
        // nonce, uint256 fee)`.
        byte_string encoded;
        encoded += abi_encode_uint(u64_be{NETWORK_CHAIN_ID});
        encoded += abi_encode_uint(u256_be{4 * 32});
        encoded += abi_encode_uint(u256_be{0});
        encoded += abi_encode_uint(u256_be{9});
        encoded += abi_encode_bytes(ciphertext);
        return EventBuilder(
                   HUB,
                   abi_encode_event_signature(
                       "EncryptedL1MessageRecorded(uint64,uint64,address,"
                       "bytes,uint256,uint256)"))
            .add_topic(abi_encode_uint(u64_be{DOMAIN}))
            .add_topic(abi_encode_address(MESSAGE_FROM))
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

    Result<DomainInputs> scan(std::span<Receipt const> const receipts)
    {
        return scan_domain_inputs(l1_header(), receipts, HUB, DOMAIN);
    }
}

TEST(ScanDomainInputs, extracts_solidity_reference_sequenced_payload)
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
    EXPECT_EQ(
        result.value(),
        inputs_of({SequencedDomainPayload{
            .payload = byte_string{0xde, 0xad, 0xbe, 0xef}, .fee = 5}}));
}

TEST(ScanDomainInputs, extracts_registration)
{
    std::array const receipts{receipt_with({make_registered()})};

    auto const result = scan(receipts);

    ASSERT_TRUE(result.has_value());
    auto expected = inputs_of({});
    expected.registered = true;
    EXPECT_EQ(result.value(), expected);
}

TEST(ScanDomainInputs, extracts_solidity_reference_l1_message)
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
    EXPECT_EQ(
        result.value(),
        inputs_of({L1DomainMessage{
            .source_chain_id = NETWORK_CHAIN_ID,
            .from = MESSAGE_FROM,
            .to = MESSAGE_TO,
            .data = byte_string{0xde, 0xad, 0xbe, 0xef},
            .nonce = 7,
            .fee = 9}}));
}

TEST(ScanDomainInputs, records_encrypted_l1_messages)
{
    // Not delivered, but each one is an input, which gives the domain a
    // block.
    std::array const receipts{receipt_with(
        {make_encrypted_message(byte_string{1, 2, 3}),
         make_encrypted_message(byte_string{})})};

    auto const result = scan(receipts);

    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(
        result.value(),
        inputs_of({EncryptedL1DomainMessage{}, EncryptedL1DomainMessage{}}));
}

TEST(ScanDomainInputs, keeps_receipt_and_log_order)
{
    std::array const receipts{
        receipt_with(
            {make_sequenced(byte_string{1}),
             make_message(byte_string{0xa}, 0),
             make_sequenced(byte_string{2})}),
        receipt_with(
            {make_encrypted_message(byte_string{0xb}),
             make_sequenced(byte_string{3})})};

    auto const result = scan(receipts);

    ASSERT_TRUE(result.has_value());
    auto const &inputs = result.value().inputs;
    ASSERT_EQ(inputs.size(), 5);
    EXPECT_EQ(
        std::get<SequencedDomainPayload>(inputs[0]).payload, byte_string{1});
    EXPECT_EQ(std::get<L1DomainMessage>(inputs[1]).data, byte_string{0xa});
    EXPECT_EQ(
        std::get<SequencedDomainPayload>(inputs[2]).payload, byte_string{2});
    EXPECT_TRUE(std::holds_alternative<EncryptedL1DomainMessage>(inputs[3]));
    EXPECT_EQ(
        std::get<SequencedDomainPayload>(inputs[4]).payload, byte_string{3});
}

TEST(ScanDomainInputs, accepts_payload_sizes_across_words)
{
    for (size_t const size : {0uz, 1uz, 31uz, 32uz, 33uz, 64uz, 65uz}) {
        byte_string const payload(size, 0x5a);
        std::array const receipts{receipt_with({make_sequenced(payload)})};

        auto const result = scan(receipts);

        ASSERT_TRUE(result.has_value()) << size;
        EXPECT_EQ(
            result.value(),
            inputs_of({SequencedDomainPayload{.payload = payload, .fee = 5}}))
            << size;
    }
}

TEST(ScanDomainInputs, receipt_bloom_skips_log_scan)
{
    auto receipt = receipt_with({make_sequenced(byte_string{1})});
    receipt.bloom = {};
    std::array const receipts{receipt};

    auto const result = scan(receipts);

    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result.value(), inputs_of({}));
}

TEST(ScanDomainInputs, header_bloom_tells_blocks_without_inputs)
{
    auto header = l1_header();
    EXPECT_FALSE(may_have_domain_inputs(header, HUB, DOMAIN));

    populate_bloom(header.logs_bloom, make_sequenced(byte_string{1}));
    EXPECT_TRUE(may_have_domain_inputs(header, HUB, DOMAIN));
    EXPECT_FALSE(may_have_domain_inputs(header, HUB, DOMAIN + 1));
    EXPECT_FALSE(may_have_domain_inputs(header, Address{0xbad}, DOMAIN));
}

TEST(ScanDomainInputs, filters_emitter_and_other_domains)
{
    auto wrong_emitter = make_sequenced(byte_string{1});
    wrong_emitter.address = Address{1};
    // Malformed, but of another domain.
    auto other_domain = make_sequenced(byte_string{2}, OTHER_DOMAIN);
    other_domain.data.pop_back();
    // Not the domain's topic: its low 64 bits alone are the domain's.
    auto dirty_domain_topic = make_sequenced(byte_string{3});
    dirty_domain_topic.topics[1].bytes[0] = 1;
    std::array const receipts{receipt_with(
        {wrong_emitter,
         other_domain,
         make_registered(OTHER_DOMAIN),
         dirty_domain_topic})};

    auto const result = scan(receipts);

    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result.value(), inputs_of({}));
}

TEST(ScanDomainInputs, rejects_malformed_events_of_the_domain)
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

    auto encrypted_truncated = make_encrypted_message(byte_string{1, 2, 3});
    encrypted_truncated.data.pop_back();

    for (auto const &log :
         {truncated,
          trailing,
          bad_offset,
          dirty_padding,
          missing_topic,
          registered_extra_data,
          encrypted_truncated}) {
        std::array const receipts{receipt_with({log})};
        EXPECT_TRUE(scan(receipts).has_error());
    }
}
