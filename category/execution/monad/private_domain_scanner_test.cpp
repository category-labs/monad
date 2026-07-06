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
