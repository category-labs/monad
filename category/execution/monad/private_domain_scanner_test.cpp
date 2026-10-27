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

#include <algorithm>
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
    constexpr Address SEQUENCER =
        0x1234567890abcdef1234567890abcdef12345678_address;
    constexpr bytes32_t STATE_ROOT =
        0xabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcd_bytes32;

    Receipt::Log make_state_update(
        uint64_t const domain_chain_id = DOMAIN_CHAIN_ID,
        uint64_t const domain_block_number = 42)
    {
        constexpr bytes32_t signature = abi_encode_event_signature(
            "DomainStateUpdated(uint64,uint256,uint64,bytes32,bytes32)");
        return EventBuilder(SEQUENCER, signature)
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
                                   "address,bytes,uint256,bytes32)");
    constexpr bytes32_t ENCRYPTED_L1_MESSAGE_RECORDED_SIGNATURE =
        abi_encode_event_signature(
            "EncryptedL1MessageRecorded(uint64,uint64,address,bytes,uint256)");

    Receipt::Log make_l1_message(
        byte_string_view const data, uint64_t const nonce = 7,
        uint64_t const domain_chain_id = DOMAIN_CHAIN_ID,
        uint64_t const source_chain_id = NETWORK_CHAIN_ID)
    {
        // Non-indexed `(uint64 sourceChainId, bytes data, uint256 nonce,
        // bytes32 messageHash)`: the dynamic bytes follow the four head words.
        byte_string encoded;
        encoded += abi_encode_uint(u64_be{source_chain_id});
        encoded += abi_encode_uint(u256_be{4 * 32});
        encoded += abi_encode_uint(u256_be{nonce});
        encoded += bytes32_t{0xab};
        encoded += abi_encode_bytes(data);
        return EventBuilder(SEQUENCER, L1_MESSAGE_RECORDED_SIGNATURE)
            .add_topic(abi_encode_uint(u64_be{domain_chain_id}))
            .add_topic(abi_encode_address(MESSAGE_FROM))
            .add_topic(abi_encode_address(MESSAGE_TO))
            .add_data(encoded)
            .build();
    }

    Receipt::Log make_encrypted_l1_message(
        byte_string_view const ciphertext, uint64_t const nonce = 8,
        uint64_t const domain_chain_id = DOMAIN_CHAIN_ID,
        uint64_t const source_chain_id = NETWORK_CHAIN_ID)
    {
        // Non-indexed `(uint64 sourceChainId, bytes ciphertext, uint256
        // nonce)`.
        byte_string encoded;
        encoded += abi_encode_uint(u64_be{source_chain_id});
        encoded += abi_encode_uint(u256_be{3 * 32});
        encoded += abi_encode_uint(u256_be{nonce});
        encoded += abi_encode_bytes(ciphertext);
        return EventBuilder(SEQUENCER, ENCRYPTED_L1_MESSAGE_RECORDED_SIGNATURE)
            .add_topic(abi_encode_uint(u64_be{domain_chain_id}))
            .add_topic(abi_encode_address(MESSAGE_FROM))
            .add_data(encoded)
            .build();
    }

    Result<std::vector<L1DomainMessage>>
    scan_messages(std::span<Receipt const> const receipts)
    {
        std::array<uint64_t, 1> const ids{DOMAIN_CHAIN_ID};
        return scan_l1_domain_messages(receipts, SEQUENCER, ids);
    }

    byte_string make_calldata(
        uint64_t const domain_chain_id, byte_string_view const payload)
    {
        constexpr uint32_t selector =
            abi_encode_selector("sequenceToDomain(uint64,bytes)");
        byte_string calldata{
            static_cast<uint8_t>(selector >> 24),
            static_cast<uint8_t>(selector >> 16),
            static_cast<uint8_t>(selector >> 8),
            static_cast<uint8_t>(selector)};
        AbiEncoder encoder;
        encoder.add_uint(u64_be{domain_chain_id});
        encoder.add_bytes(payload);
        calldata += encoder.encode_final();
        return calldata;
    }

    Transaction make_transaction(
        uint64_t const domain_chain_id = DOMAIN_CHAIN_ID,
        byte_string const &payload = byte_string{0x01, 0x02, 0x03})
    {
        return Transaction{
            .sc = {.chain_id = NETWORK_CHAIN_ID},
            .gas_limit = 123456,
            .to = SEQUENCER,
            .data = make_calldata(domain_chain_id, payload)};
    }

    byte_string solidity_reference_calldata()
    {
        // Generated independently with eth_abi 5.1.0:
        // keccak(signature)[:4] + encode(["uint64", "bytes"], values)
        return *from_hex(
            "c791e98a"
            "0000000000000000000000000000000000000000000000000000000000114eaf"
            "0000000000000000000000000000000000000000000000000000000000000040"
            "0000000000000000000000000000000000000000000000000000000000000004"
            "deadbeef00000000000000000000000000000000000000000000000000000000");
    }

    Result<std::optional<PrivateDomainPayloadView>> extract(
        Transaction const &tx,
        std::span<uint64_t const> const ids = std::span<uint64_t const>{
            &DOMAIN_CHAIN_ID, 1})
    {
        return extract_private_domain_payload(
            tx, uint256_t{NETWORK_CHAIN_ID}, SEQUENCER, ids);
    }

    void expect_not_candidate(
        Result<std::optional<PrivateDomainPayloadView>> const &result)
    {
        ASSERT_FALSE(result.has_error());
        EXPECT_FALSE(result.value().has_value());
    }
}

TEST(PrivateDomainScanner, extracts_borrowed_payload_and_l1_gas_limit)
{
    byte_string const raw_payload{0xde, 0xad, 0xbe, 0xef};
    Transaction const tx = make_transaction(DOMAIN_CHAIN_ID, raw_payload);

    auto const result = extract(tx);

    ASSERT_FALSE(result.has_error());
    ASSERT_TRUE(result.value().has_value());
    auto const &payload = *result.value();
    EXPECT_EQ(payload.domain_chain_id, DOMAIN_CHAIN_ID);
    EXPECT_EQ(payload.l1_gas_limit, tx.gas_limit);
    EXPECT_TRUE(std::ranges::equal(payload.raw_payload, raw_payload));
    EXPECT_EQ(payload.raw_payload.data(), tx.data.data() + 100);
}

TEST(PrivateDomainScanner, decodes_solidity_reference_calldata)
{
    Transaction tx = make_transaction();
    tx.data = solidity_reference_calldata();

    auto const result = extract(tx);

    ASSERT_FALSE(result.has_error());
    ASSERT_TRUE(result.value().has_value());
    auto const &payload = *result.value();
    EXPECT_EQ(payload.domain_chain_id, DOMAIN_CHAIN_ID);
    EXPECT_TRUE(std::ranges::equal(payload.raw_payload, *from_hex("deadbeef")));
    EXPECT_EQ(payload.raw_payload.data(), tx.data.data() + 100);
}

TEST(PrivateDomainScanner, accepts_empty_opaque_payload)
{
    Transaction const tx = make_transaction(DOMAIN_CHAIN_ID, {});

    auto const result = extract(tx);

    ASSERT_FALSE(result.has_error());
    ASSERT_TRUE(result.value().has_value());
    EXPECT_TRUE(result.value()->raw_payload.empty());
}

TEST(PrivateDomainScanner, accepts_canonical_payload_sizes)
{
    for (size_t const size : {1uz, 32uz, 33uz, 64uz}) {
        byte_string const raw_payload(size, 0xab);
        Transaction const tx = make_transaction(DOMAIN_CHAIN_ID, raw_payload);

        auto const result = extract(tx);

        ASSERT_FALSE(result.has_error()) << "payload size " << size;
        ASSERT_TRUE(result.value().has_value()) << "payload size " << size;
        EXPECT_TRUE(
            std::ranges::equal(result.value()->raw_payload, raw_payload));
    }
}

TEST(PrivateDomainScanner, filters_before_abi_decoding)
{
    Transaction tx = make_transaction();

    tx.to.reset();
    expect_not_candidate(extract(tx));

    tx = make_transaction();
    tx.to = Address{1};
    expect_not_candidate(extract(tx));

    tx = make_transaction();
    tx.data[0] ^= 0xff;
    expect_not_candidate(extract(tx));

    tx = make_transaction();
    tx.sc.chain_id.reset();
    expect_not_candidate(extract(tx));

    tx = make_transaction();
    tx.sc.chain_id = NETWORK_CHAIN_ID + 1;
    expect_not_candidate(extract(tx));

    tx = make_transaction(DOMAIN_CHAIN_ID + 1);
    expect_not_candidate(extract(tx));

    std::span<uint64_t const> const empty_ids;
    tx = make_transaction();
    expect_not_candidate(extract(tx, empty_ids));
}

TEST(PrivateDomainScanner, rejects_noncanonical_uint64_padding)
{
    Transaction tx = make_transaction();
    tx.data[4] = 1;

    auto const result = extract(tx);

    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), AbiDecodeError::InvalidEncoding);
}

TEST(PrivateDomainScanner, rejects_noncanonical_dynamic_bytes_offset)
{
    Transaction tx = make_transaction();
    tx.data[67] = 0x60;

    auto const result = extract(tx);

    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), AbiDecodeError::InvalidEncoding);
}

TEST(PrivateDomainScanner, rejects_invalid_bytes_length)
{
    Transaction tx = make_transaction();
    tx.data[68] = 1;
    EXPECT_TRUE(extract(tx).has_error());

    tx = make_transaction();
    tx.data[99] = 64;
    EXPECT_TRUE(extract(tx).has_error());

    tx = make_transaction();
    tx.data.resize(tx.data.size() - 1);
    EXPECT_TRUE(extract(tx).has_error());
}

TEST(PrivateDomainScanner, rejects_trailing_calldata)
{
    Transaction tx = make_transaction();
    tx.data.push_back(0xaa);

    auto const result = extract(tx);

    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), AbiDecodeError::InputTooLong);
}

TEST(PrivateDomainScanner, rejects_nonzero_dynamic_bytes_padding)
{
    Transaction tx = make_transaction();
    tx.data.back() = 1;

    auto const result = extract(tx);

    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), AbiDecodeError::InvalidEncoding);
}

TEST(PrivateDomainScanner, uses_linear_ownership_check)
{
    std::array<uint64_t, 4> const ids{DOMAIN_CHAIN_ID, 7, DOMAIN_CHAIN_ID, 3};
    Transaction const tx = make_transaction();

    auto const result = extract(tx, ids);

    ASSERT_FALSE(result.has_error());
    EXPECT_TRUE(result.value().has_value());
}

TEST(PrivateDomainScanner, returns_flat_borrowed_payloads_in_l1_order)
{
    constexpr uint64_t OTHER_DOMAIN = DOMAIN_CHAIN_ID + 1;
    std::array<uint64_t, 2> const ids{DOMAIN_CHAIN_ID, OTHER_DOMAIN};
    std::array<Transaction, 3> const l1_transactions{
        make_transaction(DOMAIN_CHAIN_ID, byte_string{10}),
        make_transaction(OTHER_DOMAIN, byte_string{20}),
        make_transaction(DOMAIN_CHAIN_ID, byte_string{30})};

    auto payloads = scan_private_domain_payloads(
        l1_transactions, 7, NETWORK_CHAIN_ID, SEQUENCER, ids);

    ASSERT_EQ(payloads.size(), 3);
    EXPECT_EQ(payloads[0].domain_chain_id, DOMAIN_CHAIN_ID);
    EXPECT_EQ(payloads[1].domain_chain_id, OTHER_DOMAIN);
    EXPECT_EQ(payloads[2].domain_chain_id, DOMAIN_CHAIN_ID);
    for (size_t i = 0; i < payloads.size(); ++i) {
        EXPECT_EQ(payloads[i].l1_transaction_index, i);
        ASSERT_EQ(payloads[i].raw_payload.size(), 1);
        EXPECT_EQ(payloads[i].raw_payload[0], (i + 1) * 10);
        EXPECT_EQ(
            payloads[i].raw_payload.data(),
            l1_transactions[i].data.data() + 100);
    }
}

TEST(PrivateDomainScanner, extracts_domain_state_update)
{
    Receipt receipt;
    receipt.add_log(make_state_update());
    std::array<uint64_t, 1> const ids{DOMAIN_CHAIN_ID};

    auto const result =
        scan_domain_state_updates(std::span{&receipt, 1}, SEQUENCER, ids);

    ASSERT_TRUE(result.has_value());
    ASSERT_EQ(result.value().size(), 1);
    EXPECT_EQ(
        result.value()[0],
        (DomainStateUpdate{
            .domain_chain_id = DOMAIN_CHAIN_ID,
            .domain_block_number = 42,
            .new_state_root = STATE_ROOT}));
}

TEST(PrivateDomainScanner, receipt_bloom_skips_log_scan)
{
    Receipt receipt;
    receipt.add_log(make_state_update());
    std::array<uint64_t, 1> const ids{DOMAIN_CHAIN_ID};

    receipt.bloom = {};
    auto const result =
        scan_domain_state_updates(std::span{&receipt, 1}, SEQUENCER, ids);

    ASSERT_TRUE(result.has_value());
    EXPECT_TRUE(result.value().empty());
}

TEST(PrivateDomainScanner, filters_emitter_and_unconfigured_domain)
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
        scan_domain_state_updates(std::span{&receipt, 1}, SEQUENCER, ids);

    ASSERT_TRUE(result.has_value());
    EXPECT_TRUE(result.value().empty());
}

TEST(PrivateDomainScanner, rejects_malformed_authentic_event)
{
    Receipt receipt;
    auto malformed = make_state_update();
    malformed.data.pop_back();
    receipt.add_log(malformed);
    std::array<uint64_t, 1> const ids{DOMAIN_CHAIN_ID};

    auto result =
        scan_domain_state_updates(std::span{&receipt, 1}, SEQUENCER, ids);
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
        scan_domain_state_updates(std::span{&receipt, 1}, SEQUENCER, ids);

    ASSERT_TRUE(result.has_value());
    ASSERT_EQ(result.value().size(), 1);
    EXPECT_EQ(result.value()[0].domain_chain_id, DOMAIN_CHAIN_ID);
    EXPECT_EQ(result.value()[0].domain_block_number, 42);
}

TEST(PrivateDomainScanner, extracts_solidity_reference_l1_message)
{
    // Non-indexed data generated independently with
    // `cast abi-encode "f(uint64,bytes,uint256,bytes32)" 20143 0xdeadbeef 7
    //  0xab..ab`.
    Receipt::Log log = make_l1_message({});
    log.data = *from_hex(
        "0000000000000000000000000000000000000000000000000000000000004eaf"
        "0000000000000000000000000000000000000000000000000000000000000080"
        "0000000000000000000000000000000000000000000000000000000000000007"
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
            .encrypted = false,
            .l1_transaction_index = 0}));
}

TEST(PrivateDomainScanner, extracts_solidity_reference_encrypted_l1_message)
{
    // `cast abi-encode "f(uint64,bytes,uint256)" 20143 0x0102030405 8`.
    Receipt::Log log = make_encrypted_l1_message({});
    log.data = *from_hex(
        "0000000000000000000000000000000000000000000000000000000000004eaf"
        "0000000000000000000000000000000000000000000000000000000000000060"
        "0000000000000000000000000000000000000000000000000000000000000008"
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
            .encrypted = true,
            .l1_transaction_index = 0}));
}

TEST(PrivateDomainScanner, passes_forwarded_message_source_chain_id_through)
{
    // A message the hub forwarded from another domain names that domain, not
    // the L1 chain, as its authenticated source.
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
    wrong_offset.data[32 + 31] = 0x60;
    expect_rejected(wrong_offset);

    auto oversized_length = make_encrypted_l1_message({});
    oversized_length.data[3 * 32 + 31] = 1;
    expect_rejected(oversized_length);

    auto missing_topic = make_l1_message({});
    missing_topic.topics.pop_back();
    expect_rejected(missing_topic);

    auto extra_topic = make_encrypted_l1_message({});
    extra_topic.topics.push_back(bytes32_t{});
    expect_rejected(extra_topic);
}
