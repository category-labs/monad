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

#include <category/core/assert.h>
#include <category/core/keccak.hpp>
#include <category/execution/domain/chain_id.hpp>
#include <category/execution/domain/derive_domain_block.hpp>
#include <category/execution/domain/hpke.hpp>
#include <category/execution/domain/inputs.hpp>
#include <category/execution/domain/system_transaction.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>

#include <secp256k1.h>
#include <secp256k1_recovery.h>

#include <gtest/gtest.h>

#include <cstdint>
#include <optional>
#include <utility>
#include <vector>

using namespace monad;
using namespace monad::domain;
using namespace monad::literals;

namespace
{
    constexpr uint64_t NETWORK_CHAIN_ID = 20143;
    constexpr uint64_t DOMAIN =
        (1u << NETWORK_CHAIN_ID_BITS) | NETWORK_CHAIN_ID;
    constexpr uint64_t OTHER_DOMAIN =
        (2u << NETWORK_CHAIN_ID_BITS) | NETWORK_CHAIN_ID;
    constexpr Address SPOKE =
        0x5FbDB2315678afecb367f032d93F642f64180aa3_address;
    constexpr Address MESSAGE_FROM =
        0x1111111111111111111111111111111111111111_address;
    constexpr Address MESSAGE_TO =
        0x2222222222222222222222222222222222222222_address;
    constexpr uint64_t TX_GAS_LIMIT = 100'000;
    // Buys TX_GAS_LIMIT gas exactly.
    constexpr uint256_t TX_FEE = DOMAIN_GAS_PRICE * TX_GAS_LIMIT;
    constexpr uint256_t MESSAGE_FEE = DOMAIN_GAS_PRICE * 300'000;
    constexpr bytes32_t SENDER_KEY{0x42};
    constexpr bytes32_t SYSTEM_SENDER_KEY =
        0xb0358e6d701a955d9926676f227e40172763296b317ff554e49cdf2c2c35f8a7_bytes32;

    Secp256k1Signature
    sign_hash(bytes32_t const &key, byte_string_view const encoding)
    {
        static secp256k1_context *const context =
            secp256k1_context_create(SECP256K1_CONTEXT_SIGN);
        auto const hash = keccak256(encoding);
        secp256k1_ecdsa_recoverable_signature signature;
        MONAD_ASSERT(
            secp256k1_ecdsa_sign_recoverable(
                context, &signature, hash.bytes, key.bytes, nullptr, nullptr) ==
            1);
        uint8_t compact[64];
        int recovery_id = 0;
        secp256k1_ecdsa_recoverable_signature_serialize_compact(
            context, compact, &recovery_id, &signature);
        return Secp256k1Signature{
            .r = load_be_unsafe<uint256_t>(compact),
            .s = load_be_unsafe<uint256_t>(compact + 32),
            .y_parity = static_cast<uint8_t>(recovery_id)};
    }

    Transaction sign(Transaction tx, bytes32_t const &key = SENDER_KEY)
    {
        tx.sc.signature =
            sign_hash(key, rlp::encode_transaction_for_signing(tx));
        return tx;
    }

    // An EIP-7702 transaction from SENDER_KEY, authorized by `authority_key`.
    Transaction authorizing_tx(bytes32_t const &authority_key)
    {
        AuthorizationEntry authorization{
            .sc = {.chain_id = uint256_t{DOMAIN}}, .address = Address{0xdef}};
        authorization.sc.signature = sign_hash(
            authority_key,
            rlp::encode_authorization_entry_for_signing(authorization));
        return sign(Transaction{
            .sc = {.chain_id = uint256_t{DOMAIN}},
            .max_fee_per_gas = DOMAIN_GAS_PRICE,
            .gas_limit = TX_GAS_LIMIT,
            .to = Address{0xabc},
            .type = TransactionType::eip7702,
            .authorization_list = {authorization}});
    }

    Transaction domain_tx(
        uint64_t const nonce, uint64_t const chain_id = DOMAIN,
        uint64_t const gas_limit = TX_GAS_LIMIT)
    {
        return sign(Transaction{
            .sc = {.chain_id = uint256_t{chain_id}},
            .nonce = nonce,
            .max_fee_per_gas = DOMAIN_GAS_PRICE,
            .gas_limit = gas_limit,
            .to = Address{0xabc},
            .type = TransactionType::eip1559,
            .data = byte_string{0x01, 0x02}});
    }

    // The stub opener "seals" by prefixing the frame byte, so these tests
    // exercise derivation independent of HPKE.
    byte_string seal(byte_string_view const plaintext)
    {
        byte_string sealed{0x01};
        sealed += plaintext;
        return sealed;
    }

    Result<byte_string> stub_open(byte_string_view const payload)
    {
        if (payload.empty() || payload[0] != 0x01) {
            return PrivateDomainHpkeError::DecryptionFailed;
        }
        return byte_string{payload.substr(1)};
    }

    SequencedDomainPayload
    sequenced(byte_string_view const payload, uint256_t const &fee = TX_FEE)
    {
        return SequencedDomainPayload{
            .payload = byte_string{payload}, .fee = fee};
    }

    SequencedDomainPayload
    sequenced_tx(Transaction const &tx, uint256_t const &fee = TX_FEE)
    {
        return sequenced(seal(rlp::encode_transaction(tx)), fee);
    }

    L1DomainMessage message(
        byte_string_view const data, uint256_t const &nonce,
        uint256_t const &fee = MESSAGE_FEE)
    {
        return L1DomainMessage{
            .source_chain_id = NETWORK_CHAIN_ID,
            .from = MESSAGE_FROM,
            .to = MESSAGE_TO,
            .data = byte_string{data},
            .nonce = nonce,
            .fee = fee};
    }

    Transaction delivery(
        byte_string_view const data, uint64_t const nonce,
        uint64_t const gas_limit = 300'000)
    {
        return make_domain_system_transaction(
            DOMAIN,
            SPOKE,
            DOMAIN_GAS_PRICE,
            gas_limit,
            NETWORK_CHAIN_ID,
            MESSAGE_FROM,
            MESSAGE_TO,
            data,
            nonce);
    }

    // The domain's inputs in one L1 block.
    DomainInputs
    l1_block(std::vector<DomainInput> inputs, bool const registered = false)
    {
        return DomainInputs{
            .l1_block_number = 100,
            .timestamp = 1'700'000'000,
            .prev_randao = bytes32_t{0x77},
            .slot_number = 4'242,
            .registered = registered,
            .inputs = std::move(inputs)};
    }

    constexpr DomainConfig CONFIG{.chain_id = DOMAIN, .spoke = SPOKE};

    // Derives for a domain whose next block is `next_domain_block`:
    // 0 before its registration.
    Result<std::optional<DerivedDomainBlock>>
    derive(DomainInputs const &inputs, uint64_t const next_domain_block = 5)
    {
        return derive_domain_block(
            inputs, CONFIG, next_domain_block, stub_open);
    }
}

TEST(DeriveDomainBlock, prices_gas_by_fee)
{
    EXPECT_EQ(purchased_domain_gas(0), 0);
    EXPECT_EQ(purchased_domain_gas(DOMAIN_GAS_PRICE - 1), 0);
    EXPECT_EQ(purchased_domain_gas(TX_FEE), TX_GAS_LIMIT);
    EXPECT_EQ(
        purchased_domain_gas(TX_FEE + DOMAIN_GAS_PRICE - 1), TX_GAS_LIMIT);
    EXPECT_EQ(
        purchased_domain_gas(DOMAIN_GAS_PRICE * DOMAIN_BLOCK_GAS_LIMIT * 2),
        DOMAIN_BLOCK_GAS_LIMIT);
    EXPECT_EQ(purchased_domain_gas(~uint256_t{}), DOMAIN_BLOCK_GAS_LIMIT);
}

TEST(DeriveDomainBlock, registration_yields_empty_genesis)
{
    auto const result = derive(l1_block({}, true), 0);

    ASSERT_TRUE(result.has_value());
    ASSERT_TRUE(result.value().has_value());
    EXPECT_EQ(
        *result.value(),
        (DerivedDomainBlock{
            .number = 0,
            .l1_block_number = 100,
            .timestamp = 1'700'000'000,
            .prev_randao = bytes32_t{0x77},
            .slot_number = 4'242}));
}

TEST(DeriveDomainBlock, genesis_holds_inputs_of_registration_block)
{
    auto const result = derive(
        l1_block(
            {sequenced_tx(domain_tx(0)), message(byte_string{0xaa}, 0)}, true),
        0);

    ASSERT_TRUE(result.has_value());
    ASSERT_TRUE(result.value().has_value());
    auto const &genesis = *result.value();
    std::vector<Transaction> const expected{
        domain_tx(0), delivery(byte_string{0xaa}, 0)};
    EXPECT_EQ(genesis.number, 0);
    EXPECT_EQ(genesis.transactions, expected);
}

TEST(DeriveDomainBlock, orders_sequenced_before_messages)
{
    auto const result = derive(l1_block(
        {message(byte_string{0xaa}, 3),
         sequenced_tx(domain_tx(0)),
         sequenced_tx(domain_tx(1))}));

    ASSERT_TRUE(result.has_value());
    ASSERT_TRUE(result.value().has_value());
    auto const &derived = *result.value();
    auto const sender = recover_sender(domain_tx(0));
    ASSERT_TRUE(sender.has_value());

    std::vector<Transaction> const expected{
        domain_tx(0), domain_tx(1), delivery(byte_string{0xaa}, 3)};
    EXPECT_EQ(derived.transactions, expected);
    EXPECT_EQ(
        derived.senders,
        (std::vector<Address>{*sender, *sender, DOMAIN_SYSTEM_RELAYER}));
    EXPECT_EQ(derived.number, 5);
    EXPECT_EQ(derived.l1_block_number, 100);
    EXPECT_EQ(derived.timestamp, 1'700'000'000);
    EXPECT_EQ(derived.prev_randao, bytes32_t{0x77});
    EXPECT_EQ(derived.slot_number, 4'242);
}

TEST(DeriveDomainBlock, bounds_gas_by_fee)
{
    auto const result = derive(l1_block(
        {// Exactly the gas its fee bought.
         sequenced_tx(domain_tx(0)),
         // One more than its fee bought.
         sequenced_tx(domain_tx(1, DOMAIN, TX_GAS_LIMIT + 1)),
         // A message gets all the gas its fee bought.
         message(byte_string{0xbb}, 0, DOMAIN_GAS_PRICE * 250'000 + 1)}));

    ASSERT_TRUE(result.has_value());
    ASSERT_TRUE(result.value().has_value());
    std::vector<Transaction> const expected{
        domain_tx(0), delivery(byte_string{0xbb}, 0, 250'000)};
    EXPECT_EQ(result.value()->transactions, expected);
}

TEST(DeriveDomainBlock, keeps_block_when_every_item_is_dropped)
{
    auto trailing = seal(rlp::encode_transaction(domain_tx(0)));
    trailing.push_back(0);

    auto const result =
        derive(l1_block({// Does not open.
                         sequenced(rlp::encode_transaction(domain_tx(0))),
                         // Does not decode, or decodes with trailing bytes.
                         sequenced(seal(byte_string{0xde, 0xad})),
                         sequenced(trailing),
                         // Another chain id.
                         sequenced_tx(domain_tx(0, OTHER_DOMAIN)),
                         sequenced_tx(domain_tx(0, NETWORK_CHAIN_ID)),
                         // No fee, so no gas.
                         sequenced_tx(domain_tx(0), 0),
                         // From the system sender, whose key is public.
                         sequenced_tx(sign(domain_tx(0), SYSTEM_SENDER_KEY)),
                         // Authorized by the system sender.
                         sequenced_tx(authorizing_tx(SYSTEM_SENDER_KEY)),
                         // Message nonce beyond 64 bits.
                         message(byte_string{}, uint256_t{1} << 64)}));

    // Lock-step: the hub sequenced work for the domain, so it gets a block.
    ASSERT_TRUE(result.has_value());
    ASSERT_TRUE(result.value().has_value());
    auto const &derived = *result.value();
    EXPECT_EQ(derived.number, 5);
    EXPECT_TRUE(derived.transactions.empty());
    EXPECT_TRUE(derived.senders.empty());
}

TEST(DeriveDomainBlock, encrypted_message_alone_yields_a_block)
{
    auto const result = derive(l1_block(
        {EncryptedL1DomainMessage{},
         message(byte_string{0xaa}, 1),
         EncryptedL1DomainMessage{}}));

    // Not delivered, but still the domain's input: the block exists, and the
    // plaintext message keeps its hub nonce.
    ASSERT_TRUE(result.has_value());
    ASSERT_TRUE(result.value().has_value());
    auto const &derived = *result.value();
    EXPECT_EQ(derived.number, 5);
    EXPECT_EQ(
        derived.transactions, (std::vector{delivery(byte_string{0xaa}, 1)}));

    auto const empty = derive(l1_block({EncryptedL1DomainMessage{}}));
    ASSERT_TRUE(empty.has_value());
    ASSERT_TRUE(empty.value().has_value());
    EXPECT_TRUE(empty.value()->transactions.empty());
}

TEST(DeriveDomainBlock, no_block_without_inputs)
{
    auto const result = derive(l1_block({}));
    ASSERT_TRUE(result.has_value());
    EXPECT_FALSE(result.value().has_value());

    auto const unregistered = derive(l1_block({}), 0);
    ASSERT_TRUE(unregistered.has_value());
    EXPECT_FALSE(unregistered.value().has_value());
}

TEST(DeriveDomainBlock, fails_on_inputs_before_registration)
{
    auto const result = derive(
        l1_block({sequenced_tx(domain_tx(0)), message(byte_string{}, 0)}), 0);

    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), DomainDerivationError::NotRegistered);
}

TEST(DeriveDomainBlock, fails_on_a_second_registration)
{
    auto const result = derive(l1_block({}, true));

    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), DomainDerivationError::AlreadyRegistered);
}
