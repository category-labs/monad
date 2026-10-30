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

#include <category/execution/monad/private_domain_derivation.hpp>

#include <category/core/assert.h>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/contract/events.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/db/ordered_trie.hpp>
#include <category/execution/monad/private_domain_hpke.hpp>
#include <category/execution/monad/private_domain_system_transaction.hpp>

#include <secp256k1.h>
#include <secp256k1_recovery.h>

#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <optional>
#include <vector>

using namespace monad;
using namespace monad::literals;

namespace
{
    constexpr uint64_t NETWORK_CHAIN_ID = 20143;
    constexpr uint64_t DOMAIN = (1u << 16) | NETWORK_CHAIN_ID;
    constexpr uint64_t OTHER_DOMAIN = (2u << 16) | NETWORK_CHAIN_ID;
    constexpr Address HUB = 0x1234567890abcdef1234567890abcdef12345678_address;
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
    constexpr bytes32_t L1_BLOCK_ID{0xb1};
    constexpr bytes32_t SENDER_KEY{0x42};

    BlockHeader l1_header()
    {
        return BlockHeader{
            .prev_randao = bytes32_t{0x77},
            .number = 100,
            .gas_limit = 300'000'000,
            .timestamp = 1'700'000'000,
            .base_fee_per_gas = 100'000'000'000};
    }

    Transaction sign(Transaction tx)
    {
        static secp256k1_context *const context =
            secp256k1_context_create(SECP256K1_CONTEXT_SIGN);
        auto const hash = keccak256(rlp::encode_transaction_for_signing(tx));
        secp256k1_ecdsa_recoverable_signature signature;
        MONAD_ASSERT(
            secp256k1_ecdsa_sign_recoverable(
                context,
                &signature,
                hash.bytes,
                SENDER_KEY.bytes,
                nullptr,
                nullptr) == 1);
        uint8_t compact[64];
        int recovery_id = 0;
        secp256k1_ecdsa_recoverable_signature_serialize_compact(
            context, compact, &recovery_id, &signature);
        tx.sc.signature.r = load_be_unsafe<uint256_t>(compact);
        tx.sc.signature.s = load_be_unsafe<uint256_t>(compact + 32);
        tx.sc.signature.y_parity = static_cast<uint8_t>(recovery_id);
        return tx;
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

    Result<byte_string>
    stub_open(uint64_t const domain_chain_id, byte_string_view const payload)
    {
        if (domain_chain_id != DOMAIN && domain_chain_id != OTHER_DOMAIN) {
            return PrivateDomainHpkeError::DecryptionFailed;
        }
        if (payload.empty() || payload[0] != 0x01) {
            return PrivateDomainHpkeError::DecryptionFailed;
        }
        return byte_string{payload.substr(1)};
    }

    Receipt::Log registered(uint64_t const domain = DOMAIN)
    {
        return EventBuilder(
                   HUB,
                   abi_encode_event_signature(
                       "DomainRegistered(uint64,address,uint64)"))
            .add_topic(abi_encode_uint(u64_be{domain}))
            .add_topic(abi_encode_address(Address{0xfee}))
            .add_data(abi_encode_uint(u64_be{100}))
            .build();
    }

    Receipt::Log sequenced(
        byte_string_view const payload, uint64_t const domain = DOMAIN,
        uint256_t const &fee = TX_FEE)
    {
        byte_string data;
        data += abi_encode_uint(u256_be{2 * 32});
        data += abi_encode_uint(u256_be{fee});
        data += abi_encode_bytes(payload);
        return EventBuilder(
                   HUB,
                   abi_encode_event_signature(
                       "DomainTransactionSequenced(uint64,bytes,uint256)"))
            .add_topic(abi_encode_uint(u64_be{domain}))
            .add_data(data)
            .build();
    }

    Receipt::Log sequenced_tx(
        Transaction const &tx, uint64_t const domain = DOMAIN,
        uint256_t const &fee = TX_FEE)
    {
        return sequenced(seal(rlp::encode_transaction(tx)), domain, fee);
    }

    Receipt::Log message(
        byte_string_view const data, uint256_t const nonce,
        uint256_t const &fee = MESSAGE_FEE)
    {
        byte_string encoded;
        encoded += abi_encode_uint(u64_be{NETWORK_CHAIN_ID});
        encoded += abi_encode_uint(u256_be{5 * 32});
        encoded += abi_encode_uint(u256_be{nonce});
        encoded += abi_encode_uint(u256_be{fee});
        encoded += bytes32_t{0xab};
        encoded += abi_encode_bytes(data);
        return EventBuilder(
                   HUB,
                   abi_encode_event_signature(
                       "L1MessageRecorded(uint64,uint64,address,address,bytes,"
                       "uint256,uint256,bytes32)"))
            .add_topic(abi_encode_uint(u64_be{DOMAIN}))
            .add_topic(abi_encode_address(MESSAGE_FROM))
            .add_topic(abi_encode_address(MESSAGE_TO))
            .add_data(encoded)
            .build();
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

    // One receipt per L1 transaction.
    struct L1Block
    {
        BlockHeader header = l1_header();
        std::vector<Receipt> receipts;

        void add(std::vector<Receipt::Log> const &logs)
        {
            Receipt receipt;
            for (auto const &log : logs) {
                receipt.add_log(log);
            }
            receipts.push_back(std::move(receipt));
        }

        Result<std::vector<DerivedDomainBlock>>
        derive(std::span<DomainDerivationState const> const domains) const
        {
            return derive_domain_blocks(
                DomainDerivationInput{
                    .l1_header = header,
                    .l1_block_id = L1_BLOCK_ID,
                    .l1_receipts = receipts,
                    .domain_hub = HUB},
                domains,
                stub_open);
        }
    };

    ProposedDomainHeader parent_header(uint64_t const number = 4)
    {
        return ProposedDomainHeader{
            .domain_chain_id = DOMAIN, .number = number};
    }

    std::array<DomainDerivationState, 1> const REGISTERED{DomainDerivationState{
        .domain_chain_id = DOMAIN,
        .spoke = SPOKE,
        .latest_header = parent_header()}};

    std::array<DomainDerivationState, 1> const UNREGISTERED{
        DomainDerivationState{.domain_chain_id = DOMAIN, .spoke = SPOKE}};

    bytes32_t transactions_root(std::vector<Transaction> const &txs)
    {
        std::vector<byte_string> encoded;
        for (auto const &tx : txs) {
            encoded.push_back(rlp::encode_transaction(tx));
        }
        return ordered_trie_root(encoded);
    }
}

TEST(PrivateDomainDerivation, prices_gas_by_fee)
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

TEST(PrivateDomainDerivation, registration_yields_empty_genesis)
{
    L1Block l1;
    l1.add({registered()});

    auto const result = l1.derive(UNREGISTERED);

    ASSERT_TRUE(result.has_value());
    ASSERT_EQ(result.value().size(), 1);
    auto const &genesis = result.value()[0];
    EXPECT_TRUE(genesis.block.transactions.empty());
    EXPECT_TRUE(genesis.senders.empty());
    EXPECT_EQ(
        genesis.block.header,
        (ProposedDomainHeader{
            .domain_chain_id = DOMAIN,
            .number = 0,
            .l1_block_number = 100,
            .l1_block_id = L1_BLOCK_ID,
            .timestamp = 1'700'000'000,
            .mix_hash = bytes32_t{0x77},
            .gas_limit = DOMAIN_BLOCK_GAS_LIMIT,
            .base_fee_per_gas = DOMAIN_GAS_PRICE,
            .transactions_root = NULL_ROOT}));
}

TEST(PrivateDomainDerivation, genesis_holds_events_of_registration_block)
{
    L1Block l1;
    l1.add({registered()});
    l1.add({sequenced_tx(domain_tx(0)), message(byte_string{0xaa}, 0)});

    auto const result = l1.derive(UNREGISTERED);

    ASSERT_TRUE(result.has_value());
    ASSERT_EQ(result.value().size(), 1);
    auto const &genesis = result.value()[0];
    std::vector<Transaction> const expected{
        domain_tx(0), delivery(byte_string{0xaa}, 0)};
    EXPECT_EQ(genesis.block.header.number, 0);
    EXPECT_EQ(genesis.block.transactions, expected);
    EXPECT_EQ(
        genesis.block.header.transactions_root, transactions_root(expected));
}

TEST(PrivateDomainDerivation, orders_sequenced_before_messages)
{
    L1Block l1;
    l1.add({message(byte_string{0xaa}, 3), sequenced_tx(domain_tx(0))});
    l1.add({sequenced_tx(domain_tx(1))});

    auto const result = l1.derive(REGISTERED);

    ASSERT_TRUE(result.has_value());
    ASSERT_EQ(result.value().size(), 1);
    auto const &derived = result.value()[0];
    auto const sender = recover_sender(domain_tx(0));
    ASSERT_TRUE(sender.has_value());

    std::vector<Transaction> const expected{
        domain_tx(0), domain_tx(1), delivery(byte_string{0xaa}, 3)};
    EXPECT_EQ(derived.block.transactions, expected);
    EXPECT_EQ(
        derived.senders,
        (std::vector<Address>{*sender, *sender, DOMAIN_SYSTEM_RELAYER}));
    EXPECT_EQ(derived.block.header.number, 5);
    EXPECT_EQ(derived.block.header.l1_block_number, 100);
    EXPECT_EQ(derived.block.header.l1_block_id, L1_BLOCK_ID);
    EXPECT_EQ(derived.block.header.gas_limit, DOMAIN_BLOCK_GAS_LIMIT);
    EXPECT_EQ(derived.block.header.base_fee_per_gas, DOMAIN_GAS_PRICE);
    EXPECT_EQ(
        derived.block.header.transactions_root, transactions_root(expected));
}

TEST(PrivateDomainDerivation, bounds_gas_by_fee)
{
    L1Block l1;
    l1.add({// Exactly the gas its fee bought.
            sequenced_tx(domain_tx(0)),
            // One more than its fee bought.
            sequenced_tx(domain_tx(1, DOMAIN, TX_GAS_LIMIT + 1)),
            // A message gets all the gas its fee bought.
            message(byte_string{0xbb}, 0, DOMAIN_GAS_PRICE * 250'000 + 1)});

    auto const result = l1.derive(REGISTERED);

    ASSERT_TRUE(result.has_value());
    ASSERT_EQ(result.value().size(), 1);
    std::vector<Transaction> const expected{
        domain_tx(0), delivery(byte_string{0xbb}, 0, 250'000)};
    EXPECT_EQ(result.value()[0].block.transactions, expected);
}

TEST(PrivateDomainDerivation, keeps_block_when_every_item_is_dropped)
{
    auto trailing = seal(rlp::encode_transaction(domain_tx(0)));
    trailing.push_back(0);

    L1Block l1;
    l1.add({// Does not open.
            sequenced(rlp::encode_transaction(domain_tx(0))),
            // Does not decode, or decodes with trailing bytes.
            sequenced(seal(byte_string{0xde, 0xad})),
            sequenced(trailing),
            // Another chain id.
            sequenced_tx(domain_tx(0, OTHER_DOMAIN)),
            sequenced_tx(domain_tx(0, NETWORK_CHAIN_ID)),
            // No fee, so no gas.
            sequenced_tx(domain_tx(0), DOMAIN, 0),
            // Message nonce beyond 64 bits.
            message(byte_string{}, uint256_t{1} << 64)});

    auto const result = l1.derive(REGISTERED);

    // Lock-step: the hub sequenced work for the domain, so it gets a block.
    ASSERT_TRUE(result.has_value());
    ASSERT_EQ(result.value().size(), 1);
    auto const &derived = result.value()[0];
    EXPECT_EQ(derived.block.header.number, 5);
    EXPECT_TRUE(derived.block.transactions.empty());
    EXPECT_TRUE(derived.senders.empty());
    EXPECT_EQ(derived.block.header.transactions_root, NULL_ROOT);
}

TEST(PrivateDomainDerivation, skips_domain_without_genesis)
{
    L1Block l1;
    l1.add({sequenced_tx(domain_tx(0)), message(byte_string{}, 0)});

    auto const result = l1.derive(UNREGISTERED);

    ASSERT_TRUE(result.has_value());
    EXPECT_TRUE(result.value().empty());
}

TEST(PrivateDomainDerivation, no_block_without_events)
{
    L1Block l1;
    l1.add({});
    // Events of a domain this node does not serve.
    l1.add({sequenced_tx(domain_tx(0, OTHER_DOMAIN), OTHER_DOMAIN)});

    auto const result = l1.derive(REGISTERED);

    ASSERT_TRUE(result.has_value());
    EXPECT_TRUE(result.value().empty());
}

TEST(PrivateDomainDerivation, derives_domains_independently)
{
    std::array const domains{
        DomainDerivationState{
            .domain_chain_id = DOMAIN,
            .spoke = SPOKE,
            .latest_header = parent_header(9)},
        DomainDerivationState{
            .domain_chain_id = OTHER_DOMAIN, .spoke = Address{0x5}}};
    L1Block l1;
    l1.add({sequenced_tx(domain_tx(0)), registered(OTHER_DOMAIN)});

    auto const result = l1.derive(domains);

    ASSERT_TRUE(result.has_value());
    ASSERT_EQ(result.value().size(), 2);
    EXPECT_EQ(result.value()[0].block.header.domain_chain_id, DOMAIN);
    EXPECT_EQ(result.value()[0].block.header.number, 10);
    EXPECT_EQ(result.value()[0].block.transactions.size(), 1);
    EXPECT_EQ(result.value()[1].block.header.domain_chain_id, OTHER_DOMAIN);
    EXPECT_EQ(result.value()[1].block.header.number, 0);
    EXPECT_TRUE(result.value()[1].block.transactions.empty());
}

TEST(PrivateDomainDerivation, fails_on_malformed_hub_event)
{
    auto malformed = sequenced(byte_string{1});
    malformed.data.pop_back();
    L1Block l1;
    l1.add({malformed});

    EXPECT_TRUE(l1.derive(REGISTERED).has_error());
}
