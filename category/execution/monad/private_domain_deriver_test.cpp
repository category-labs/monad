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

#include <category/execution/monad/private_domain_deriver.hpp>

#include <category/async/config.hpp>
#include <category/async/util.hpp>
#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/contract/events.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/monad/private_domain_block_store.hpp>
#include <category/execution/monad/private_domain_derivation.hpp>
#include <category/execution/monad/private_domain_hpke.hpp>
#include <category/execution/monad/private_domain_l1_source.hpp>
#include <category/execution/monad/private_domain_system_transaction.hpp>
#include <category/mpt/db_error.hpp>

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

    // A finalized L1 chain whose history starts at `earliest`.
    class FakeL1Source final : public L1Source
    {
    public:
        std::vector<L1Block> blocks;
        std::optional<uint64_t> finalized;
        uint64_t earliest{0};

        void add(std::vector<Receipt::Log> const &logs)
        {
            L1Block block;
            block.header = BlockHeader{
                .number = blocks.size(), .timestamp = 1'000 + blocks.size()};
            block.hash = bytes32_t{blocks.size() + 1};
            for (auto const &log : logs) {
                Receipt receipt;
                receipt.add_log(log);
                block.receipts.push_back(std::move(receipt));
            }
            blocks.push_back(std::move(block));
        }

        std::optional<uint64_t> latest_finalized() const override
        {
            return finalized;
        }

        Result<L1Block> read_finalized(uint64_t const number) const override
        {
            if (number < earliest) {
                return mpt::DbError::version_no_longer_exist;
            }
            return blocks.at(number);
        }
    };

    class PrivateDomainDeriverTest : public ::testing::Test
    {
    protected:
        std::filesystem::path dir_;
        PrivateDomainKeyring keyring_;
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
            std::array const configs{PrivateDomainConfig{
                .domain_chain_id = DOMAIN,
                .spoke_address = SPOKE,
                .private_key_path = dir_ / "domain.pem"}};
            auto keyring = PrivateDomainKeyring::load(configs);
            ASSERT_TRUE(keyring.has_value());
            keyring_ = std::move(keyring).value();
        }

        void TearDown() override
        {
            std::filesystem::remove_all(dir_);
        }

        // Derives until the deriver has caught up with the finalized chain.
        void derive_all(PrivateDomainDeriver &deriver)
        {
            while (true) {
                auto const derived = deriver.derive_next();
                ASSERT_TRUE(derived.has_value());
                if (!derived.value()) {
                    return;
                }
            }
        }
    };
}

TEST_F(PrivateDomainDeriverTest, derives_the_finalized_chain_into_the_store)
{
    byte_string const data{0xca, 0xfe};
    l1_.add({});
    l1_.add({registered()});
    l1_.add({});
    l1_.add({message(data, 0)});
    l1_.add({message(data, 1)});

    DomainBlockStore store{dir_ / "store"};
    PrivateDomainDeriver deriver{l1_, store, keyring_, HUB, 0};
    EXPECT_EQ(deriver.derive_next().value(), false);

    l1_.finalized = 3;
    derive_all(deriver);
    EXPECT_EQ(deriver.next_l1_block(), 4);
    EXPECT_EQ(store.l1_cursor(), 3);
    ASSERT_TRUE(store.tip().has_value());
    EXPECT_EQ(store.tip()->header.number, 1);
    EXPECT_EQ(store.tip()->header.l1_block_number, 3);
    EXPECT_EQ(store.tip()->header.l1_block_hash, bytes32_t{4});
    EXPECT_EQ(store.tip()->transactions, (std::vector{delivery(data, 0)}));
    EXPECT_EQ(store.get(0)->header.l1_block_number, 1);
}

TEST_F(PrivateDomainDeriverTest, continues_after_a_restart)
{
    byte_string const data{0xca, 0xfe};
    l1_.add({registered()});
    l1_.add({});
    l1_.add({message(data, 0)});
    l1_.finalized = 1;
    {
        DomainBlockStore store{dir_ / "store"};
        PrivateDomainDeriver deriver{l1_, store, keyring_, HUB, 0};
        derive_all(deriver);
    }

    l1_.finalized = 2;
    DomainBlockStore store{dir_ / "store"};
    // The start block only applies to an empty store.
    PrivateDomainDeriver deriver{l1_, store, keyring_, HUB, 0};
    EXPECT_EQ(deriver.next_l1_block(), 2);
    derive_all(deriver);
    EXPECT_EQ(store.tip()->header.number, 1);
    EXPECT_EQ(store.tip()->header.l1_block_number, 2);
}

// A crash between appending a block and moving the cursor.
TEST_F(PrivateDomainDeriverTest, continues_after_a_tip_past_the_cursor)
{
    l1_.add({registered()});
    l1_.add({});
    l1_.add({message(byte_string{0xaa}, 0)});
    l1_.finalized = 2;
    {
        DomainBlockStore store{dir_ / "store"};
        PrivateDomainDeriver deriver{l1_, store, keyring_, HUB, 0};
        derive_all(deriver);
        store.set_l1_cursor(0);
    }

    DomainBlockStore store{dir_ / "store"};
    PrivateDomainDeriver const deriver{l1_, store, keyring_, HUB, 0};
    EXPECT_EQ(deriver.next_l1_block(), 3);
}

TEST_F(PrivateDomainDeriverTest, fails_once_the_next_block_left_l1_history)
{
    l1_.add({});
    l1_.add({registered()});
    l1_.finalized = 1;
    l1_.earliest = 1;

    DomainBlockStore store{dir_ / "store"};
    PrivateDomainDeriver deriver{l1_, store, keyring_, HUB, 0};
    auto const derived = deriver.derive_next();
    ASSERT_TRUE(derived.has_error());
    EXPECT_EQ(derived.error(), mpt::DbError::version_no_longer_exist);
    EXPECT_EQ(deriver.next_l1_block(), 0);
    EXPECT_EQ(store.l1_cursor(), std::nullopt);
}
