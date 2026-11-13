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

#include <category/execution/domain/deriver.hpp>

#include <category/async/config.hpp>
#include <category/async/util.hpp>
#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/derivation_error.hpp>
#include <category/execution/domain/derive_domain_block.hpp>
#include <category/execution/domain/domain_block.hpp>
#include <category/execution/domain/hpke.hpp>
#include <category/execution/domain/l1_source.hpp>
#include <category/execution/domain/system_transaction.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/contract/events.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/mpt/db_error.hpp>
#include <category/mpt/util.hpp>

#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <optional>
#include <string>
#include <string_view>
#include <unistd.h>
#include <utility>
#include <vector>

using namespace monad;
using namespace monad::domain;
using namespace monad::literals;

namespace
{
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

    Receipt::Log message(byte_string_view const data, uint64_t const nonce)
    {
        byte_string encoded;
        encoded += abi_encode_uint(u64_be{NETWORK_CHAIN_ID});
        encoded += abi_encode_uint(u256_be{5 * 32});
        encoded += abi_encode_uint(u256_be{nonce});
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

    Transaction delivery(byte_string_view const data, uint64_t const nonce)
    {
        return make_domain_system_transaction(
            DOMAIN,
            SPOKE,
            DOMAIN_GAS_PRICE,
            300'000,
            NETWORK_CHAIN_ID,
            MESSAGE_FROM,
            MESSAGE_TO,
            data,
            nonce);
    }

    // A finalized L1 chain whose history starts at `history_start`, with the
    // hub's record of the domain's latest block as of each L1 block.
    class FakeL1Source final : public L1Source
    {
    public:
        struct Block
        {
            BlockHeader header;
            std::vector<Receipt> receipts;
        };

        std::vector<Block> blocks;
        std::vector<bytes32_t> latest_domain_block;
        uint64_t finalized{mpt::INVALID_BLOCK_NUM};
        uint64_t history_start{0};
        // Blocks whose receipts were read.
        mutable std::vector<uint64_t> receipt_reads;

        // An L1 block with `logs`, each in a receipt of its own. As the hub
        // does, a block that registers the domain is its block 0, and any
        // other with logs is its next block.
        void add(std::vector<Receipt::Log> const &logs)
        {
            bytes32_t word =
                blocks.empty() ? bytes32_t{} : latest_domain_block.back();
            if (!logs.empty()) {
                uint64_t const number =
                    word == bytes32_t{}
                        ? 0
                        : load_be_unsafe<uint64_t>(word.bytes + 24) + 1;
                word = bytes32_t{};
                // Gas sold: not read.
                word.bytes[15] = 1;
                store_be(word.bytes + 16, uint64_t{blocks.size()});
                store_be(word.bytes + 24, number);
            }
            latest_domain_block.push_back(word);
            Block block;
            block.header = BlockHeader{
                .number = blocks.size(), .timestamp = 1'000 + blocks.size()};
            for (auto const &log : logs) {
                Receipt receipt;
                receipt.add_log(log);
                populate_bloom(block.header.logs_bloom, log);
                block.receipts.push_back(std::move(receipt));
            }
            blocks.push_back(std::move(block));
        }

        uint64_t latest_finalized() const override
        {
            return finalized;
        }

        Result<BlockHeader>
        read_finalized_header(uint64_t const number) const override
        {
            if (number < history_start) {
                return mpt::DbError::version_no_longer_exist;
            }
            return blocks.at(number).header;
        }

        Result<std::vector<Receipt>>
        read_finalized_receipts(uint64_t const number) const override
        {
            if (number < history_start) {
                return mpt::DbError::version_no_longer_exist;
            }
            receipt_reads.push_back(number);
            return blocks.at(number).receipts;
        }

        uint64_t earliest() const override
        {
            return history_start;
        }

        Result<bytes32_t> read_storage(
            uint64_t const number, Address const &address,
            bytes32_t const &slot) const override
        {
            if (number < history_start || number > finalized) {
                return mpt::DbError::version_no_longer_exist;
            }
            if (address != HUB || slot != latest_domain_block_slot(DOMAIN)) {
                return bytes32_t{};
            }
            return latest_domain_block.at(number);
        }
    };

    class PrivateDomainDeriverTest : public ::testing::Test
    {
    protected:
        std::filesystem::path dir_;
        std::optional<PrivateDomainKey> key_;
        FakeL1Source l1_;

        void SetUp() override
        {
            std::string pattern =
                (MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
                 "private_domain_deriver_XXXXXX")
                    .string();
            ASSERT_NE(::mkdtemp(pattern.data()), nullptr);
            dir_ = pattern;
            std::ofstream{dir_ / "domain.pem"} << DOMAIN_KEY;
            auto key = PrivateDomainKey::load(dir_ / "domain.pem");
            ASSERT_TRUE(key.has_value());
            key_.emplace(std::move(key).value());
        }

        void TearDown() override
        {
            std::filesystem::remove_all(dir_);
        }

        PrivateDomainDeriver
        make_deriver(DerivationCursor cursor = DerivationCursor{})
        {
            return PrivateDomainDeriver{l1_, *key_, DOMAIN, SPOKE, HUB, cursor};
        }

        // Derives until the deriver has caught up with the finalized chain,
        // and returns the blocks it handed on.
        std::vector<DerivedDomainBlock>
        derive_all(PrivateDomainDeriver &deriver)
        {
            std::vector<DerivedDomainBlock> blocks;
            while (true) {
                auto const derived = deriver.derive_next(
                    [&](DerivedDomainBlock const &block) -> Result<void> {
                        blocks.push_back(block);
                        return outcome::success();
                    });
                EXPECT_TRUE(derived.has_value());
                if (!derived.has_value() || !derived.value()) {
                    return blocks;
                }
            }
        }
    };
}

TEST(PrivateDomainDerivationStart, reads_the_hub_slot_of_the_domain)
{
    // cast keccak $(cast abi-encode "f(uint64,string)" 89060441869999
    //     "monad.domains.input-queue"), low 7 bits cleared.
    EXPECT_EQ(
        latest_domain_block_slot(DOMAIN),
        0xe5c326caf8a97b93042ade5f2dab865145ca7b8bdca70ab8e41ac0f6e3e48a80_bytes32);
}

TEST_F(PrivateDomainDeriverTest, starts_after_the_latest_block_until_registered)
{
    auto const none = find_derivation_start(l1_, HUB, DOMAIN, 0);
    ASSERT_TRUE(none.has_value());
    EXPECT_EQ(none.value(), DerivationCursor{});
    auto const ahead = find_derivation_start(l1_, HUB, DOMAIN, 1);
    ASSERT_TRUE(ahead.has_error());
    EXPECT_EQ(ahead.error(), DomainDerivationError::AheadOfHub);

    l1_.add({});
    l1_.add({});
    l1_.finalized = 1;
    auto const start = find_derivation_start(l1_, HUB, DOMAIN, 0);
    ASSERT_TRUE(start.has_value());
    EXPECT_EQ(start.value(), DerivationCursor{.next_l1_block = 2});
}

TEST_F(PrivateDomainDeriverTest, finds_where_the_next_block_is_derived_from)
{
    byte_string const data{0xca, 0xfe};
    l1_.add({});
    l1_.add({registered()});
    l1_.add({});
    l1_.add({message(data, 0)});
    l1_.add({});
    l1_.add({message(data, 1)});
    l1_.add({});
    l1_.finalized = 6;

    auto const start = [&](uint64_t const next_block) {
        auto const cursor = find_derivation_start(l1_, HUB, DOMAIN, next_block);
        EXPECT_TRUE(cursor.has_value());
        return cursor.has_value() ? cursor.value() : DerivationCursor{};
    };
    // No blocks: from the registration.
    EXPECT_EQ(start(0), DerivationCursor{.next_l1_block = 1});
    EXPECT_EQ(
        start(1), (DerivationCursor{.next_l1_block = 3, .next_block = 1}));
    EXPECT_EQ(
        start(2), (DerivationCursor{.next_l1_block = 5, .next_block = 2}));
    // Everything executed: after the latest finalized block.
    EXPECT_EQ(
        start(3), (DerivationCursor{.next_l1_block = 7, .next_block = 3}));

    // The hub is behind the domain.
    auto const ahead = find_derivation_start(l1_, HUB, DOMAIN, 4);
    ASSERT_TRUE(ahead.has_error());
    EXPECT_EQ(ahead.error(), DomainDerivationError::AheadOfHub);

    // Block 1's L1 block is the oldest the source has, then older than it.
    l1_.history_start = 3;
    EXPECT_EQ(
        start(1), (DerivationCursor{.next_l1_block = 3, .next_block = 1}));
    l1_.history_start = 4;
    auto const expired = find_derivation_start(l1_, HUB, DOMAIN, 1);
    ASSERT_TRUE(expired.has_error());
    EXPECT_EQ(expired.error(), mpt::DbError::version_no_longer_exist);
    auto const no_genesis = find_derivation_start(l1_, HUB, DOMAIN, 0);
    ASSERT_TRUE(no_genesis.has_error());
    EXPECT_EQ(no_genesis.error(), mpt::DbError::version_no_longer_exist);
    EXPECT_EQ(
        start(2), (DerivationCursor{.next_l1_block = 5, .next_block = 2}));
}

TEST_F(PrivateDomainDeriverTest, hands_on_the_finalized_chain)
{
    byte_string const data{0xca, 0xfe};
    l1_.add({});
    l1_.add({registered()});
    l1_.add({});
    l1_.add({message(data, 0)});
    l1_.add({message(data, 1)});

    auto deriver = make_deriver();
    EXPECT_TRUE(derive_all(deriver).empty());

    l1_.finalized = 3;
    auto const blocks = derive_all(deriver);
    ASSERT_EQ(blocks.size(), 2);
    EXPECT_EQ(blocks[0].number, 0);
    EXPECT_EQ(blocks[0].l1_block_number, 1);
    EXPECT_EQ(blocks[0].timestamp, 1'001);
    EXPECT_EQ(blocks[1].number, 1);
    EXPECT_EQ(blocks[1].l1_block_number, 3);
    EXPECT_EQ(blocks[1].transactions, (std::vector{delivery(data, 0)}));

    EXPECT_EQ(deriver.cursor().next_l1_block, 4);
    EXPECT_EQ(deriver.cursor().next_block, 2);
    // Only the blocks with the domain's events had their receipts read.
    EXPECT_EQ(l1_.receipt_reads, (std::vector<uint64_t>{1, 3}));
}

TEST_F(PrivateDomainDeriverTest, continues_after_a_restart)
{
    byte_string const data{0xca, 0xfe};
    l1_.add({registered()});
    l1_.add({});
    l1_.add({message(data, 0)});
    l1_.finalized = 1;
    std::vector<DerivedDomainBlock> first;
    {
        auto deriver = make_deriver();
        first = derive_all(deriver);
    }
    ASSERT_EQ(first.size(), 1);

    // A restart finds its place from the block after its last.
    l1_.finalized = 2;
    auto const cursor =
        find_derivation_start(l1_, HUB, DOMAIN, first[0].number + 1);
    ASSERT_TRUE(cursor.has_value());
    EXPECT_EQ(
        cursor.value(),
        (DerivationCursor{.next_l1_block = 2, .next_block = 1}));
    auto deriver = make_deriver(cursor.value());
    auto const blocks = derive_all(deriver);
    ASSERT_EQ(blocks.size(), 1);
    EXPECT_EQ(blocks[0].number, 1);
    EXPECT_EQ(blocks[0].l1_block_number, 2);
}

TEST_F(PrivateDomainDeriverTest, a_failed_handler_keeps_the_cursor)
{
    l1_.add({registered()});
    l1_.finalized = 0;

    auto deriver = make_deriver();
    auto const failed =
        deriver.derive_next([](DerivedDomainBlock const &) -> Result<void> {
            // Any error.
            return mpt::DbError::version_no_longer_exist;
        });
    ASSERT_TRUE(failed.has_error());
    EXPECT_EQ(deriver.cursor(), DerivationCursor{});

    // The same block, again.
    auto const blocks = derive_all(deriver);
    ASSERT_EQ(blocks.size(), 1);
    EXPECT_EQ(blocks[0].number, 0);
}

TEST_F(PrivateDomainDeriverTest, fails_once_the_next_block_left_l1_history)
{
    l1_.add({});
    l1_.add({registered()});
    l1_.finalized = 1;
    l1_.history_start = 1;

    auto deriver = make_deriver();
    auto const derived =
        deriver.derive_next([](DerivedDomainBlock const &) -> Result<void> {
            return outcome::success();
        });
    ASSERT_TRUE(derived.has_error());
    EXPECT_EQ(derived.error(), mpt::DbError::version_no_longer_exist);
    EXPECT_EQ(deriver.cursor().next_l1_block, 0);
}

TEST_F(PrivateDomainDeriverTest, fails_on_inputs_before_registration)
{
    // Derivation started after the domain's registration.
    l1_.add({message(byte_string{0xaa}, 4)});
    l1_.finalized = 0;

    auto deriver = make_deriver();
    auto const derived =
        deriver.derive_next([](DerivedDomainBlock const &) -> Result<void> {
            return outcome::success();
        });
    ASSERT_TRUE(derived.has_error());
    EXPECT_EQ(derived.error(), DomainDerivationError::NotRegistered);
    EXPECT_EQ(deriver.cursor(), DerivationCursor{});
}
