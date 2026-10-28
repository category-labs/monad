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

#include <category/execution/monad/private_domains.hpp>

#include <category/core/hex.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/contract/events.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/monad/core/rlp/domain_block_rlp.hpp>
#include <category/execution/monad/db/commit_block.hpp>
#include <category/execution/monad/private_domain_system_transaction.hpp>
#include <category/statesync/statesync_server_context.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>

#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <memory>
#include <optional>
#include <ranges>
#include <string_view>
#include <unistd.h>
#include <vector>

using namespace monad;
using namespace monad::literals;

namespace
{
    using traits = MonadTraits<MONAD_TEN>;

    constexpr uint64_t NETWORK_CHAIN_ID = 20143;
    constexpr uint64_t DOMAIN = 0x510000004eaf;
    constexpr Address HUB = 0x1234567890abcdef1234567890abcdef12345678_address;
    constexpr Address SPOKE =
        0x5FbDB2315678afecb367f032d93F642f64180aa3_address;
    constexpr Address MESSAGE_FROM =
        0x1111111111111111111111111111111111111111_address;
    constexpr Address MESSAGE_TO =
        0x2222222222222222222222222222222222222222_address;

    // X25519 key 0x11 * 32.
    constexpr std::string_view DOMAIN_KEY =
        R"(-----BEGIN PRIVATE KEY-----
MC4CAQAwBQYDK2VuBCIEIBERERERERERERERERERERERERERERERERERERERERER
-----END PRIVATE KEY-----
)";

    // An EIP-1559 transaction of DOMAIN (nonce 0, gas 100'000) signed by
    // secp256k1 key 0x42, and the same transaction sealed to DOMAIN_KEY with
    // an ephemeral key derived from ikm 0x55 * 32, by eth-account and pyhpke
    // 0.6.5.
    constexpr Address SENDER =
        0x6f4c950442e1Af093BcfF730381E63Ae9171b87a_address;

    byte_string signed_transaction()
    {
        return *from_hex(
            "02f87086510000004eaf8080850ba43b7400830186a094000000000000000000"
            "0000000000000000000abc80820102c080a03524410eec196ed020b64c6e2b16"
            "b18249621686c02655d096b510644ee71a27a05400ac6a0ec2d6bee704ab7aff"
            "e172fe9b86521a26d164b21bc8966dc9569f05");
    }

    byte_string sealed_transaction()
    {
        return *from_hex(
            "79d32518232dd78292aac6c8e228dadc854a35124bbcb410c24105bb8d4b522f"
            "462bd9207d1a702c2adbb70f9fc863726efacfd6109a392d21d44e3dc5ccd513"
            "b275d6a60545e1e509e5c0f34ae05111df320bcc5fbd2d065fb91d70b5ae5429"
            "140f8a8ca6e57f39bc5d685ebfa3e85618bf5ffd55bb815e023dadab453e91e4"
            "4620e887b77ec670c0dc3901767d58547d73a8484162354d178fe0e1faddb5ae"
            "27d5f5c5");
    }

    std::filesystem::path write_domain_key()
    {
        std::array<char, 64> pattern{};
        std::ranges::copy(
            std::string_view{"/tmp/monad-private-domains-test-XXXXXX"},
            pattern.begin());
        char const *const directory = ::mkdtemp(pattern.data());
        EXPECT_NE(directory, nullptr);
        auto const path = std::filesystem::path{directory} / "domain.pem";
        std::ofstream{path} << DOMAIN_KEY;
        return path;
    }

    Receipt receipt_with(std::vector<Receipt::Log> const &logs)
    {
        Receipt receipt;
        for (auto const &log : logs) {
            receipt.add_log(log);
        }
        return receipt;
    }

    Receipt::Log registered()
    {
        return EventBuilder(
                   HUB,
                   abi_encode_event_signature(
                       "DomainRegistered(uint64,address,uint64)"))
            .add_topic(abi_encode_uint(u64_be{DOMAIN}))
            .add_topic(abi_encode_address(Address{0xfee}))
            .add_data(abi_encode_uint(u64_be{100}))
            .build();
    }

    Receipt::Log sequenced(byte_string_view const payload)
    {
        byte_string data;
        data += abi_encode_uint(u256_be{2 * 32});
        data += abi_encode_uint(u256_be{DOMAIN_GAS_PRICE * 100'000});
        data += abi_encode_bytes(payload);
        return EventBuilder(
                   HUB,
                   abi_encode_event_signature(
                       "DomainTransactionSequenced(uint64,bytes,uint256)"))
            .add_topic(abi_encode_uint(u64_be{DOMAIN}))
            .add_data(data)
            .build();
    }

    Receipt::Log message(byte_string_view const data)
    {
        byte_string encoded;
        encoded += abi_encode_uint(u64_be{NETWORK_CHAIN_ID});
        encoded += abi_encode_uint(u256_be{5 * 32});
        encoded += abi_encode_uint(u256_be{0});
        encoded += abi_encode_uint(u256_be{DOMAIN_GAS_PRICE * 300'000});
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

    // Derives the domain blocks of L1 block `number` from the db's current
    // block, commits them with it and finalizes it. Like the runloops, it
    // reaches the TrieDb through the statesync server context.
    PrivateDomainBlocks commit_l1_block(
        TrieDb &tdb, PrivateDomains const *const domains, uint64_t const number,
        std::vector<Receipt> const &receipts)
    {
        // Too large for the stack.
        auto const context =
            std::make_unique<monad_statesync_server_context>(tdb);
        auto &db = *context;
        BlockHeader const header{
            .number = number,
            .gas_limit = 100'000,
            .timestamp = 1'000 + number};
        // TrieDb rejects a zero block id.
        bytes32_t const block_id{number + 1};
        auto derived = derive_private_domain_blocks(
            domains, db, header, block_id, receipts);
        EXPECT_TRUE(derived.has_value());
        commit_block<traits>(
            db,
            block_id,
            header,
            StateDeltas{},
            Code{},
            receipts,
            {},
            {},
            {},
            {},
            std::nullopt,
            derived.value().commits());
        db.finalize(number, block_id);
        db.set_block_and_prefix(number);
        return std::move(derived).value();
    }
}

TEST(PrivateDomains, derives_nothing_without_domains)
{
    mpt::Db mpt_db{std::make_unique<MonadInMemoryMachine>()};
    TrieDb tdb{mpt_db};
    std::vector<Receipt> const receipts{receipt_with({registered()})};

    auto const blocks = commit_l1_block(tdb, nullptr, 0, receipts);

    EXPECT_TRUE(blocks.blocks().empty());
    EXPECT_FALSE(blocks.commits().has_value());
    EXPECT_FALSE(tdb.has_domain_tables());
}

// A node that has no domains configured but whose db has domain tables keeps
// writing them without deriving.
TEST(PrivateDomains, writes_the_tables_without_configured_domains)
{
    mpt::Db mpt_db{std::make_unique<MonadInMemoryMachine>()};
    TrieDb tdb{mpt_db};
    PrivateDomains const domains{};
    std::vector<Receipt> const receipts{receipt_with({registered()})};

    auto const blocks = commit_l1_block(tdb, &domains, 0, receipts);

    EXPECT_TRUE(blocks.blocks().empty());
    ASSERT_TRUE(blocks.commits().has_value());
    EXPECT_TRUE(blocks.commits()->empty());
    EXPECT_TRUE(tdb.has_domain_tables());
    EXPECT_EQ(tdb.read_domain_block_header(DOMAIN), std::nullopt);
}

// The runloops' path: derive from the parent's stored header, then commit the
// domain blocks with the L1 block.
TEST(PrivateDomains, continues_from_the_committed_header)
{
    mpt::Db mpt_db{std::make_unique<MonadInMemoryMachine>()};
    TrieDb tdb{mpt_db};
    auto const key_path = write_domain_key();
    std::array const configs{PrivateDomainConfig{
        .domain_chain_id = DOMAIN,
        .spoke_address = SPOKE,
        .private_key_path = key_path}};
    auto keyring = PrivateDomainKeyring::load(configs);
    std::filesystem::remove_all(key_path.parent_path());
    ASSERT_TRUE(keyring.has_value());
    PrivateDomains const domains{
        .keyring = std::move(keyring).value(), .hub = HUB};

    commit_l1_block(tdb, &domains, 0, {});
    auto const genesis =
        commit_l1_block(tdb, &domains, 1, {receipt_with({registered()})});
    ASSERT_EQ(genesis.blocks().size(), 1);
    EXPECT_EQ(genesis.blocks()[0].block.header.number, 0);

    // A quiet L1 block leaves the domain alone.
    EXPECT_TRUE(commit_l1_block(tdb, &domains, 2, {}).blocks().empty());

    byte_string const data{0xca, 0xfe};
    auto const derived = commit_l1_block(
        tdb,
        &domains,
        3,
        {receipt_with({message(data), sequenced(sealed_transaction())})});

    ASSERT_EQ(derived.blocks().size(), 1);
    auto const &block = derived.blocks()[0];
    byte_string const signed_tx = signed_transaction();
    byte_string_view encoded{signed_tx};
    auto const transaction = rlp::decode_transaction(encoded);
    ASSERT_TRUE(transaction.has_value());
    std::vector<Transaction> const expected{
        transaction.value(),
        make_domain_system_transaction(
            DOMAIN,
            SPOKE,
            DOMAIN_GAS_PRICE,
            300'000,
            NETWORK_CHAIN_ID,
            MESSAGE_FROM,
            MESSAGE_TO,
            data,
            0)};
    EXPECT_EQ(block.block.header.number, 1);
    EXPECT_EQ(block.block.header.l1_block_number, 3);
    EXPECT_EQ(block.block.transactions, expected);
    EXPECT_EQ(block.senders, (std::vector{SENDER, DOMAIN_SYSTEM_RELAYER}));
    EXPECT_EQ(
        tdb.read_domain_block_header(DOMAIN),
        rlp::encode_proposed_domain_header(block.block.header));
}
