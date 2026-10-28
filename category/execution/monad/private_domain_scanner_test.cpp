// Copyright (C) 2026 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

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

using namespace monad;
using namespace monad::literals;

namespace
{
    constexpr uint64_t NETWORK_CHAIN_ID = 20143;
    constexpr uint64_t DOMAIN_CHAIN_ID = 0x114eaf;
    constexpr Address HUB =
        0x1234567890abcdef1234567890abcdef12345678_address;
    constexpr bytes32_t STATE_ROOT =
        0xabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcd_bytes32;

    constexpr bytes32_t DOMAIN_TRANSACTION_SEQUENCED_SIGNATURE =
        abi_encode_event_signature(
            "DomainTransactionSequenced(uint64,bytes,uint256)");

    Receipt::Log make_sequenced(
        byte_string_view const payload, uint64_t const fee = 7,
        uint64_t const domain_chain_id = DOMAIN_CHAIN_ID)
    {
        // (bytes payload, uint256 fee)
        byte_string encoded;
        encoded += abi_encode_uint(u256_be{2 * 32});
        encoded += abi_encode_uint(u256_be{fee});
        encoded += abi_encode_bytes(payload);
        return EventBuilder(HUB, DOMAIN_TRANSACTION_SEQUENCED_SIGNATURE)
            .add_topic(abi_encode_uint(u64_be{domain_chain_id}))
            .add_data(encoded)
            .build();
    }

    Receipt::Log make_state_update(
        uint64_t const domain_chain_id = DOMAIN_CHAIN_ID,
        uint64_t const domain_block_number = 42)
    {
        constexpr bytes32_t signature = abi_encode_event_signature(
            "DomainStateUpdated(uint64,uint256,uint64,bytes32,bytes32)");
        return EventBuilder(HUB, signature)
            .add_topic(abi_encode_uint(u64_be{domain_chain_id}))
            .add_data(abi_encode_uint(u256_be{7}))
            .add_data(abi_encode_uint(u64_be{domain_block_number}))
            .add_data(STATE_ROOT)
            .add_data(bytes32_t{9})
            .build();
    }

    constexpr Address MESSAGE_FROM =
        0x1111111111111111111111111111111111111111_address;
    constexpr Address MESSAGE_TO =
        0x2222222222222222222222222222222222222222_address;
    constexpr bytes32_t L1_MESSAGE_RECORDED_SIGNATURE =
        abi_encode_event_signature("L1MessageRecorded(uint64,uint64,address,"
                                   "address,bytes,uint256,uint256,bytes32)");
    constexpr bytes32_t ENCRYPTED_L1_MESSAGE_RECORDED_SIGNATURE =
        abi_encode_event_signature(
            "EncryptedL1MessageRecorded(uint64,uint64,address,bytes,uint256,"
            "uint256)");

    Receipt::Log make_l1_message(
        byte_string_view const data, uint64_t const nonce = 7,
        uint64_t const domain_chain_id = DOMAIN_CHAIN_ID,
        uint64_t const source_chain_id = NETWORK_CHAIN_ID,
        uint64_t const fee = 3)
    {
        // (uint64 sourceChainId, bytes data, uint256 nonce, uint256 fee,
        //  bytes32 messageHash)
        byte_string encoded;
        encoded += abi_encode_uint(u64_be{source_chain_id});
        encoded += abi_encode_uint(u256_be{5 * 32});
        encoded += abi_encode_uint(u256_be{nonce});
        encoded += abi_encode_uint(u256_be{fee});
        encoded += bytes32_t{0xab};
        encoded += abi_encode_bytes(data);
        return EventBuilder(HUB, L1_MESSAGE_RECORDED_SIGNATURE)
            .add_topic(abi_encode_uint(u64_be{domain_chain_id}))
            .add_topic(abi_encode_address(MESSAGE_FROM))
            .add_topic(abi_encode_address(MESSAGE_TO))
            .add_data(encoded)
            .build();
    }

    Receipt::Log make_encrypted_l1_message(
        byte_string_view const ciphertext, uint64_t const nonce = 8,
        uint64_t const domain_chain_id = DOMAIN_CHAIN_ID,
        uint64_t const source_chain_id = NETWORK_CHAIN_ID,
        uint64_t const fee = 5)
    {
        // (uint64 sourceChainId, bytes ciphertext, uint256 nonce, uint256 fee)
        byte_string encoded;
        encoded += abi_encode_uint(u64_be{source_chain_id});
        encoded += abi_encode_uint(u256_be{4 * 32});
        encoded += abi_encode_uint(u256_be{nonce});
        encoded += abi_encode_uint(u256_be{fee});
        encoded += abi_encode_bytes(ciphertext);
        return EventBuilder(HUB, ENCRYPTED_L1_MESSAGE_RECORDED_SIGNATURE)
            .add_topic(abi_encode_uint(u64_be{domain_chain_id}))
            .add_topic(abi_encode_address(MESSAGE_FROM))
            .add_data(encoded)
            .build();
    }

    Result<std::vector<SequencedDomainTransaction>>
    scan_sequenced(std::span<Receipt const> const receipts)
    {
        std::array<uint64_t, 1> const ids{DOMAIN_CHAIN_ID};
        return scan_sequenced_domain_transactions(receipts, HUB, ids);
    }

    Result<std::vector<L1DomainMessage>>
    scan_messages(std::span<Receipt const> const receipts)
    {
        std::array<uint64_t, 1> const ids{DOMAIN_CHAIN_ID};
        return scan_l1_domain_messages(receipts, HUB, ids);
    }
}

TEST(PrivateDomainScanner, extracts_solidity_reference_sequenced_transaction)
{
    // Non-indexed data generated independently with
    // `cast abi-encode "f(bytes,uint256)" 0xdeadbeef 7`.
    Receipt::Log log = make_sequenced({});
    log.data = *from_hex(
        "0000000000000000000000000000000000000000000000000000000000000040"
        "0000000000000000000000000000000000000000000000000000000000000007"
        "0000000000000000000000000000000000000000000000000000000000000004"
        "deadbeef00000000000000000000000000000000000000000000000000000000");
    Receipt receipt;
    receipt.add_log(log);

    auto const result = scan_sequenced(std::span{&receipt, 1});

    ASSERT_TRUE(result.has_value());
    ASSERT_EQ(result.value().size(), 1);
    EXPECT_EQ(
        result.value()[0],
        (SequencedDomainTransaction{
            .domain_chain_id = DOMAIN_CHAIN_ID,
            .payload = byte_string{0xde, 0xad, 0xbe, 0xef},
            .fee = 7,
            .l1_transaction_index = 0}));
}

TEST(PrivateDomainScanner, accepts_sequenced_payload_sizes_across_words)
{
    for (size_t const size : {0uz, 1uz, 31uz, 32uz, 33uz, 64uz, 100uz}) {
        byte_string const payload(size, 0xab);
        Receipt receipt;
        receipt.add_log(make_sequenced(payload));

        auto const result = scan_sequenced(std::span{&receipt, 1});

        ASSERT_TRUE(result.has_value()) << size;
        ASSERT_EQ(result.value().size(), 1) << size;
        EXPECT_EQ(result.value()[0].payload, payload);
    }
}

TEST(PrivateDomainScanner, carries_the_full_fee_word)
{
    Receipt::Log log = make_sequenced(byte_string{0x01});
    log.data[32] = 0x80;
    Receipt receipt;
    receipt.add_log(log);

    auto const result = scan_sequenced(std::span{&receipt, 1});

    ASSERT_TRUE(result.has_value());
    ASSERT_EQ(result.value().size(), 1);
    EXPECT_EQ(result.value()[0].fee, (uint256_t{1} << 255) + 7);
}

TEST(PrivateDomainScanner, returns_sequenced_transactions_in_receipt_and_log_order)
{
    constexpr uint64_t OTHER_DOMAIN = DOMAIN_CHAIN_ID + 1;
    std::array<uint64_t, 2> const ids{DOMAIN_CHAIN_ID, OTHER_DOMAIN};
    std::array<Receipt, 3> receipts;
    receipts[0].add_log(make_sequenced(byte_string{10}, 1, DOMAIN_CHAIN_ID));
    receipts[0].add_log(make_sequenced(byte_string{20}, 2, OTHER_DOMAIN));
    receipts[2].add_log(make_sequenced(byte_string{30}, 3, DOMAIN_CHAIN_ID));

    auto const result =
        scan_sequenced_domain_transactions(receipts, HUB, ids);

    ASSERT_TRUE(result.has_value());
    auto const &transactions = result.value();
    ASSERT_EQ(transactions.size(), 3);
    EXPECT_EQ(transactions[0].domain_chain_id, DOMAIN_CHAIN_ID);
    EXPECT_EQ(transactions[1].domain_chain_id, OTHER_DOMAIN);
    EXPECT_EQ(transactions[2].domain_chain_id, DOMAIN_CHAIN_ID);
    for (size_t i = 0; i < transactions.size(); ++i) {
        EXPECT_EQ(transactions[i].l1_transaction_index, i < 2 ? 0 : 2);
        EXPECT_EQ(transactions[i].fee, i + 1);
        EXPECT_EQ(transactions[i].payload, byte_string{uint8_t((i + 1) * 10)});
    }
}

TEST(PrivateDomainScanner, accepts_unsorted_duplicate_domain_ids)
{
    std::array<uint64_t, 4> const ids{DOMAIN_CHAIN_ID, 7, DOMAIN_CHAIN_ID, 3};
    Receipt receipt;
    receipt.add_log(make_sequenced(byte_string{1}));

    auto const result =
        scan_sequenced_domain_transactions(std::span{&receipt, 1}, HUB, ids);

    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result.value().size(), 1);
}

TEST(PrivateDomainScanner, sequenced_receipt_bloom_skips_log_scan)
{
    Receipt receipt;
    receipt.add_log(make_sequenced(byte_string{1}));

    receipt.bloom = {};
    auto const result = scan_sequenced(std::span{&receipt, 1});

    ASSERT_TRUE(result.has_value());
    EXPECT_TRUE(result.value().empty());
}

TEST(PrivateDomainScanner, ignores_sequenced_events_of_other_emitters_and_domains)
{
    constexpr uint64_t OTHER_DOMAIN = DOMAIN_CHAIN_ID + 1;
    Receipt receipt;
    auto wrong_emitter = make_sequenced(byte_string{1});
    wrong_emitter.address = Address{1};
    receipt.add_log(wrong_emitter);
    auto unconfigured = make_sequenced(byte_string{1}, 7, OTHER_DOMAIN);
    unconfigured.data.pop_back();
    receipt.add_log(unconfigured);
    receipt.add_log(make_l1_message({}));
    std::span<uint64_t const> const empty_ids;

    auto const result = scan_sequenced(std::span{&receipt, 1});
    ASSERT_TRUE(result.has_value());
    EXPECT_TRUE(result.value().empty());

    receipt.add_log(make_sequenced(byte_string{1}));
    auto const unserved = scan_sequenced_domain_transactions(
        std::span{&receipt, 1}, HUB, empty_ids);
    ASSERT_TRUE(unserved.has_value());
    EXPECT_TRUE(unserved.value().empty());
}

TEST(PrivateDomainScanner, rejects_malformed_authentic_sequenced_events)
{
    auto const expect_rejected = [](Receipt::Log log, AbiDecodeError const error) {
        Receipt receipt;
        receipt.add_log(log);
        auto const result = scan_sequenced(std::span{&receipt, 1});
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.assume_error(), error);
    };

    auto truncated = make_sequenced(byte_string{0xde, 0xad});
    truncated.data.pop_back();
    expect_rejected(truncated, AbiDecodeError::InputTooShort);

    auto trailing = make_sequenced(byte_string{0xde, 0xad});
    trailing.data.push_back(0);
    expect_rejected(trailing, AbiDecodeError::InputTooLong);

    auto nonzero_padding = make_sequenced(byte_string{0xde, 0xad});
    nonzero_padding.data.back() = 1;
    expect_rejected(nonzero_padding, AbiDecodeError::InvalidEncoding);

    auto wrong_offset = make_sequenced({});
    wrong_offset.data[31] = 0x60;
    expect_rejected(wrong_offset, AbiDecodeError::InvalidEncoding);

    auto oversized_length = make_sequenced({});
    oversized_length.data[2 * 32 + 31] = 1;
    expect_rejected(oversized_length, AbiDecodeError::InputTooShort);

    auto missing_topic = make_sequenced({});
    missing_topic.topics.pop_back();
    expect_rejected(missing_topic, AbiDecodeError::InvalidEncoding);

    auto extra_topic = make_sequenced({});
    extra_topic.topics.push_back(bytes32_t{});
    expect_rejected(extra_topic, AbiDecodeError::InvalidEncoding);
}

TEST(PrivateDomainScanner, extracts_domain_state_update)
{
    Receipt receipt;
    receipt.add_log(make_state_update());
    std::array<uint64_t, 1> const ids{DOMAIN_CHAIN_ID};

    auto const result =
        scan_domain_state_updates(std::span{&receipt, 1}, HUB, ids);

    ASSERT_TRUE(result.has_value());
    ASSERT_EQ(result.value().size(), 1);
    EXPECT_EQ(
        result.value()[0],
        (DomainStateUpdate{
            .domain_chain_id = DOMAIN_CHAIN_ID,
            .domain_block_number = 42,
            .new_state_root = STATE_ROOT}));
}

TEST(PrivateDomainScanner, state_update_receipt_bloom_skips_log_scan)
{
    Receipt receipt;
    receipt.add_log(make_state_update());
    std::array<uint64_t, 1> const ids{DOMAIN_CHAIN_ID};

    receipt.bloom = {};
    auto const result =
        scan_domain_state_updates(std::span{&receipt, 1}, HUB, ids);

    ASSERT_TRUE(result.has_value());
    EXPECT_TRUE(result.value().empty());
}

TEST(PrivateDomainScanner, state_update_filters_emitter_and_unconfigured_domain)
{
    constexpr uint64_t OTHER_DOMAIN = DOMAIN_CHAIN_ID + 1;
    Receipt receipt;
    auto wrong_emitter = make_state_update();
    wrong_emitter.address = Address{1};
    receipt.add_log(wrong_emitter);
    auto unconfigured = make_state_update(OTHER_DOMAIN);
    unconfigured.data.pop_back();
    receipt.add_log(unconfigured);
    std::array<uint64_t, 1> const ids{DOMAIN_CHAIN_ID};

    auto const result =
        scan_domain_state_updates(std::span{&receipt, 1}, HUB, ids);

    ASSERT_TRUE(result.has_value());
    EXPECT_TRUE(result.value().empty());
}

TEST(PrivateDomainScanner, state_update_rejects_malformed_authentic_event)
{
    Receipt receipt;
    auto malformed = make_state_update();
    malformed.data.pop_back();
    receipt.add_log(malformed);
    std::array<uint64_t, 1> const ids{DOMAIN_CHAIN_ID};

    auto result =
        scan_domain_state_updates(std::span{&receipt, 1}, HUB, ids);
    EXPECT_TRUE(result.has_error());
}

TEST(PrivateDomainScanner, ignores_uint64_high_bits)
{
    Receipt receipt;
    auto event = make_state_update();
    event.topics[1].bytes[0] = 1;
    event.data[32] = 1;
    receipt.add_log(event);
    std::array<uint64_t, 1> const ids{DOMAIN_CHAIN_ID};

    auto const result =
        scan_domain_state_updates(std::span{&receipt, 1}, HUB, ids);

    ASSERT_TRUE(result.has_value());
    ASSERT_EQ(result.value().size(), 1);
    EXPECT_EQ(result.value()[0].domain_chain_id, DOMAIN_CHAIN_ID);
    EXPECT_EQ(result.value()[0].domain_block_number, 42);
}

TEST(PrivateDomainScanner, extracts_solidity_reference_l1_message)
{
    // Non-indexed data generated independently with
    // `cast abi-encode "f(uint64,bytes,uint256,uint256,bytes32)" 20143
    //  0xdeadbeef 7 3 0xab..ab`.
    Receipt::Log log = make_l1_message({});
    log.data = *from_hex(
        "0000000000000000000000000000000000000000000000000000000000004eaf"
        "00000000000000000000000000000000000000000000000000000000000000a0"
        "0000000000000000000000000000000000000000000000000000000000000007"
        "0000000000000000000000000000000000000000000000000000000000000003"
        "abababababababababababababababababababababababababababababababab"
        "0000000000000000000000000000000000000000000000000000000000000004"
        "deadbeef00000000000000000000000000000000000000000000000000000000");
    Receipt receipt;
    receipt.add_log(log);

    auto const result = scan_messages(std::span{&receipt, 1});

    ASSERT_TRUE(result.has_value());
    ASSERT_EQ(result.value().size(), 1);
    EXPECT_EQ(
        result.value()[0],
        (L1DomainMessage{
            .domain_chain_id = DOMAIN_CHAIN_ID,
            .source_chain_id = NETWORK_CHAIN_ID,
            .from = MESSAGE_FROM,
            .to = MESSAGE_TO,
            .payload = byte_string{0xde, 0xad, 0xbe, 0xef},
            .nonce = 7,
            .fee = 3,
            .encrypted = false,
            .l1_transaction_index = 0}));
}

TEST(PrivateDomainScanner, extracts_solidity_reference_encrypted_l1_message)
{
    // `cast abi-encode "f(uint64,bytes,uint256,uint256)" 20143 0x0102030405
    //  8 5`.
    Receipt::Log log = make_encrypted_l1_message({});
    log.data = *from_hex(
        "0000000000000000000000000000000000000000000000000000000000004eaf"
        "0000000000000000000000000000000000000000000000000000000000000080"
        "0000000000000000000000000000000000000000000000000000000000000008"
        "0000000000000000000000000000000000000000000000000000000000000005"
        "0000000000000000000000000000000000000000000000000000000000000005"
        "0102030405000000000000000000000000000000000000000000000000000000");
    Receipt receipt;
    receipt.add_log(log);

    auto const result = scan_messages(std::span{&receipt, 1});

    ASSERT_TRUE(result.has_value());
    ASSERT_EQ(result.value().size(), 1);
    EXPECT_EQ(
        result.value()[0],
        (L1DomainMessage{
            .domain_chain_id = DOMAIN_CHAIN_ID,
            .source_chain_id = NETWORK_CHAIN_ID,
            .from = MESSAGE_FROM,
            .to = std::nullopt,
            .payload = byte_string{0x01, 0x02, 0x03, 0x04, 0x05},
            .nonce = 8,
            .fee = 5,
            .encrypted = true,
            .l1_transaction_index = 0}));
}

TEST(PrivateDomainScanner, passes_forwarded_message_source_chain_id_through)
{
    constexpr uint64_t SOURCE_DOMAIN = DOMAIN_CHAIN_ID + 1;
    byte_string const data{0x01};
    Receipt receipt;
    receipt.add_log(make_l1_message(data, 3, DOMAIN_CHAIN_ID, SOURCE_DOMAIN));
    receipt.add_log(
        make_encrypted_l1_message(data, 4, DOMAIN_CHAIN_ID, SOURCE_DOMAIN));

    auto const result = scan_messages(std::span{&receipt, 1});

    ASSERT_TRUE(result.has_value());
    ASSERT_EQ(result.value().size(), 2);
    EXPECT_EQ(result.value()[0].source_chain_id, SOURCE_DOMAIN);
    EXPECT_EQ(result.value()[0].domain_chain_id, DOMAIN_CHAIN_ID);
    EXPECT_EQ(result.value()[1].source_chain_id, SOURCE_DOMAIN);
    EXPECT_EQ(result.value()[1].domain_chain_id, DOMAIN_CHAIN_ID);
}

TEST(PrivateDomainScanner, accepts_message_payload_sizes_across_words)
{
    for (size_t const size : {0uz, 31uz, 32uz, 33uz, 64uz, 100uz}) {
        byte_string const data(size, 0x5a);
        Receipt receipt;
        receipt.add_log(make_l1_message(data));
        receipt.add_log(make_encrypted_l1_message(data));

        auto const result = scan_messages(std::span{&receipt, 1});

        ASSERT_TRUE(result.has_value()) << size;
        ASSERT_EQ(result.value().size(), 2) << size;
        EXPECT_EQ(result.value()[0].payload, data);
        EXPECT_EQ(result.value()[1].payload, data);
    }
}

TEST(PrivateDomainScanner, returns_messages_in_receipt_and_log_order)
{
    std::array<Receipt, 3> receipts;
    receipts[0].add_log(make_l1_message({}, 0));
    receipts[0].add_log(make_encrypted_l1_message({}, 1));
    receipts[2].add_log(make_encrypted_l1_message({}, 2));
    receipts[2].add_log(make_l1_message({}, 3));

    auto const result = scan_messages(receipts);

    ASSERT_TRUE(result.has_value());
    ASSERT_EQ(result.value().size(), 4);
    for (size_t i = 0; i < 4; ++i) {
        EXPECT_EQ(result.value()[i].nonce, i);
        EXPECT_EQ(result.value()[i].l1_transaction_index, i < 2 ? 0 : 2);
    }
    EXPECT_FALSE(result.value()[0].encrypted);
    EXPECT_TRUE(result.value()[1].encrypted);
    EXPECT_TRUE(result.value()[2].encrypted);
    EXPECT_FALSE(result.value()[3].encrypted);
}

TEST(PrivateDomainScanner, message_receipt_bloom_skips_log_scan)
{
    Receipt receipt;
    receipt.add_log(make_l1_message({}));
    receipt.add_log(make_encrypted_l1_message({}));

    receipt.bloom = {};
    auto const result = scan_messages(std::span{&receipt, 1});

    ASSERT_TRUE(result.has_value());
    EXPECT_TRUE(result.value().empty());
}

TEST(PrivateDomainScanner, filters_message_emitter_and_unconfigured_domain)
{
    constexpr uint64_t OTHER_DOMAIN = DOMAIN_CHAIN_ID + 1;
    Receipt receipt;
    auto wrong_emitter = make_l1_message({});
    wrong_emitter.address = Address{1};
    receipt.add_log(wrong_emitter);
    auto unconfigured = make_encrypted_l1_message({}, 8, OTHER_DOMAIN);
    unconfigured.data.pop_back();
    receipt.add_log(unconfigured);
    auto unrelated = make_state_update();
    receipt.add_log(unrelated);
    receipt.add_log(make_sequenced(byte_string{1}));

    auto const result = scan_messages(std::span{&receipt, 1});

    ASSERT_TRUE(result.has_value());
    EXPECT_TRUE(result.value().empty());
}

TEST(PrivateDomainScanner, rejects_malformed_authentic_message_events)
{
    auto const expect_rejected = [](Receipt::Log log) {
        Receipt receipt;
        receipt.add_log(log);
        EXPECT_TRUE(scan_messages(std::span{&receipt, 1}).has_error());
    };

    auto truncated = make_l1_message(byte_string{0xde, 0xad});
    truncated.data.pop_back();
    expect_rejected(truncated);

    auto trailing = make_encrypted_l1_message(byte_string{0xde, 0xad});
    trailing.data.push_back(0);
    expect_rejected(trailing);

    auto nonzero_padding = make_l1_message(byte_string{0xde, 0xad});
    nonzero_padding.data.back() = 1;
    expect_rejected(nonzero_padding);

    auto wrong_offset = make_l1_message({});
    wrong_offset.data[32 + 31] = 0x80;
    expect_rejected(wrong_offset);

    auto oversized_length = make_encrypted_l1_message({});
    oversized_length.data[4 * 32 + 31] = 1;
    expect_rejected(oversized_length);

    auto missing_topic = make_l1_message({});
    missing_topic.topics.pop_back();
    expect_rejected(missing_topic);

    auto extra_topic = make_encrypted_l1_message({});
    extra_topic.topics.push_back(bytes32_t{});
    expect_rejected(extra_topic);
}
