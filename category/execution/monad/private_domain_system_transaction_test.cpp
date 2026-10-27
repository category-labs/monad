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
    constexpr uint256_t BASE_FEE = 50'000'000'000;
    auto const tx = make_domain_system_transaction(
        DOMAIN_CHAIN_ID,
        SPOKE,
        BASE_FEE,
        300'000,
        NETWORK_CHAIN_ID,
        FROM,
        TO,
        byte_string{0x01},
        9);

    EXPECT_EQ(tx.type, TransactionType::legacy);
    ASSERT_TRUE(tx.sc.chain_id.has_value());
    EXPECT_EQ(*tx.sc.chain_id, uint256_t{DOMAIN_CHAIN_ID});
    // The hub message nonce doubles as the transaction nonce.
    EXPECT_EQ(tx.nonce, 9);
    EXPECT_EQ(tx.gas_limit, 300'000);
    // The base fee is the floor the shared validation enforces; the gasless
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
    EXPECT_TRUE(tx.sc.signature.is_valid());
    EXPECT_EQ(recover_sender(tx), DOMAIN_SYSTEM_RELAYER);
}

TEST(PrivateDomainSystemTransaction, signs_reference_transaction)
{
    // Generated independently with cast, which signs with the same alloy
    // signer as monad-bft's L1 system transactions:
    // cast mktx --legacy --chain 85679 --nonce 9 --gas-price 50000000000
    //   --gas-limit 300000 --value 0 --private-key <system sender key> 0x5F..a3
    //   "$(cast calldata
    //     "relayL1Message(uint64,address,address,bytes,uint256)"
    //     20143 0x11..11 0x22..22 0x01 9)"
    byte_string const expected = *from_hex(
        "f9014d09850ba43b7400830493e0945fbdb2315678afecb367f032d93f642f64180aa3"
        "80b8e470c0a876"
        "0000000000000000000000000000000000000000000000000000000000004eaf"
        "0000000000000000000000001111111111111111111111111111111111111111"
        "0000000000000000000000002222222222222222222222222222222222222222"
        "00000000000000000000000000000000000000000000000000000000000000a0"
        "0000000000000000000000000000000000000000000000000000000000000009"
        "0000000000000000000000000000000000000000000000000000000000000001"
        "0100000000000000000000000000000000000000000000000000000000000000"
        "83029d81"
        "a099e74cf5d1463412280289695b0845f72b5793b3127983f641892a327bcb2e11"
        "a04f2a6e6286ff5cdb5e04e8a596913742ec8a2e2c72aa473f9ae500c4d72294fa");
    EXPECT_EQ(
        rlp::encode_transaction(make_domain_system_transaction(
            DOMAIN_CHAIN_ID,
            SPOKE,
            50'000'000'000,
            300'000,
            NETWORK_CHAIN_ID,
            FROM,
            TO,
            byte_string{0x01},
            9)),
        expected);
}

TEST(PrivateDomainSystemTransaction, round_trips_through_rlp)
{
    auto const tx = make_domain_system_transaction(
        DOMAIN_CHAIN_ID,
        SPOKE,
        0,
        21'000,
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
        0x6f49a8F621353f12378d0046E7d7e4b9B249DC9e_address);
}
