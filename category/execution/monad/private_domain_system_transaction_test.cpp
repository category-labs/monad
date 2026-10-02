// Copyright (C) 2026 Category Labs, Inc.
// SPDX-License-Identifier: GPL-3.0-or-later

#include <category/execution/monad/private_domain_system_transaction.hpp>

#include <category/core/hex.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::literals;

namespace
{
    constexpr uint64_t NETWORK_CHAIN_ID = 20143;
    constexpr uint64_t DOMAIN_CHAIN_ID = (1u << 16) | NETWORK_CHAIN_ID;
    constexpr Address SPOKE =
        0x5FbDB2315678afecb367f032d93F642f64180aa3_address;
    constexpr Address FROM = 0x1111111111111111111111111111111111111111_address;
    constexpr Address TO = 0x2222222222222222222222222222222222222222_address;
}

TEST(PrivateDomainSystemTransaction, encodes_solidity_reference_calldata)
{
    // Generated independently with cast:
    // cast calldata "relayL1Message(uint64,address,address,bytes,uint256)"
    //   20143 0x11..11 0x22..22 0xdeadbeef 7
    byte_string const expected = *from_hex(
        "70c0a876"
        "0000000000000000000000000000000000000000000000000000000000004eaf"
        "0000000000000000000000001111111111111111111111111111111111111111"
        "0000000000000000000000002222222222222222222222222222222222222222"
        "00000000000000000000000000000000000000000000000000000000000000a0"
        "0000000000000000000000000000000000000000000000000000000000000007"
        "0000000000000000000000000000000000000000000000000000000000000004"
        "deadbeef00000000000000000000000000000000000000000000000000000000");
    EXPECT_EQ(
        encode_relay_l1_message(
            NETWORK_CHAIN_ID, FROM, TO, byte_string{0xde, 0xad, 0xbe, 0xef}, 7),
        expected);
}

TEST(PrivateDomainSystemTransaction, encodes_empty_payload_calldata)
{
    byte_string const expected = *from_hex(
        "70c0a876"
        "0000000000000000000000000000000000000000000000000000000000004eaf"
        "0000000000000000000000001111111111111111111111111111111111111111"
        "0000000000000000000000002222222222222222222222222222222222222222"
        "00000000000000000000000000000000000000000000000000000000000000a0"
        "0000000000000000000000000000000000000000000000000000000000000000"
        "0000000000000000000000000000000000000000000000000000000000000000");
    EXPECT_EQ(
        encode_relay_l1_message(NETWORK_CHAIN_ID, FROM, TO, {}, 0), expected);
}

TEST(PrivateDomainSystemTransaction, encodes_forwarded_domain_source)
{
    // A message the hub forwarded from another domain names that domain as
    // its source; the client passes it through to the spoke unchanged.
    constexpr uint64_t SOURCE_DOMAIN = (2u << 16) | NETWORK_CHAIN_ID;
    auto const calldata =
        encode_relay_l1_message(SOURCE_DOMAIN, FROM, TO, {}, 0);
    ASSERT_EQ(calldata.size(), 4 + 6 * 32);
    for (size_t i = 4; i < 4 + 29; ++i) {
        EXPECT_EQ(calldata[i], 0) << i;
    }
    EXPECT_EQ(calldata[4 + 29], 0x02);
    EXPECT_EQ(calldata[4 + 30], 0x4e);
    EXPECT_EQ(calldata[4 + 31], 0xaf);
}

TEST(PrivateDomainSystemTransaction, builds_gasless_legacy_delivery)
{
    constexpr uint256_t BASE_FEE = 100'000'000'000;
    auto const tx = make_domain_system_transaction(
        DOMAIN_CHAIN_ID,
        SPOKE,
        5,
        BASE_FEE,
        NETWORK_CHAIN_ID,
        FROM,
        TO,
        byte_string{0x01},
        9);

    EXPECT_EQ(tx.type, TransactionType::legacy);
    ASSERT_TRUE(tx.sc.chain_id.has_value());
    EXPECT_EQ(*tx.sc.chain_id, uint256_t{DOMAIN_CHAIN_ID});
    EXPECT_EQ(tx.nonce, 5);
    EXPECT_EQ(tx.gas_limit, DOMAIN_SYSTEM_TRANSACTION_GAS_LIMIT);
    // The L1 base fee is the floor the shared validation enforces; the gasless
    // path never charges it.
    EXPECT_EQ(tx.max_fee_per_gas, BASE_FEE);
    EXPECT_EQ(tx.max_priority_fee_per_gas, 0);
    EXPECT_EQ(tx.value, 0);
    ASSERT_TRUE(tx.to.has_value());
    EXPECT_EQ(*tx.to, SPOKE);
    EXPECT_EQ(
        tx.data,
        encode_relay_l1_message(
            NETWORK_CHAIN_ID, FROM, TO, byte_string{0x01}, 9));
    EXPECT_TRUE(tx.access_list.empty());
    EXPECT_TRUE(tx.authorization_list.empty());
    // Passes the shared EIP-2 well-formedness check without being a real
    // signature; the sender is pinned by the client, never recovered.
    EXPECT_TRUE(tx.sc.signature.is_valid());
    EXPECT_NE(recover_sender(tx), DOMAIN_SYSTEM_RELAYER);
}

TEST(PrivateDomainSystemTransaction, round_trips_through_rlp)
{
    auto const tx = make_domain_system_transaction(
        DOMAIN_CHAIN_ID,
        SPOKE,
        0,
        0,
        NETWORK_CHAIN_ID,
        FROM,
        TO,
        byte_string(40, 0x7f),
        1);
    auto const encoded = rlp::encode_transaction(tx);
    byte_string_view view{encoded};
    auto const decoded = rlp::decode_transaction(view);
    ASSERT_TRUE(decoded.has_value());
    EXPECT_TRUE(view.empty());
    EXPECT_EQ(decoded.value(), tx);
}

TEST(PrivateDomainSystemTransaction, relayer_matches_spoke_constant)
{
    EXPECT_EQ(
        DOMAIN_SYSTEM_RELAYER,
        0xffffFFFfFFffffffffffffffFfFFFfffFFFfFFfE_address);
}
