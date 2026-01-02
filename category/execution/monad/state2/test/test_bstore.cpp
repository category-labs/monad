// Copyright (C) 2025 Category Labs, Inc.
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
#include <category/core/unaligned.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/test/test_fixtures_gtest.hpp>
#include <category/vm/vm.hpp>

#include <optional>

#include <gtest/gtest.h>
#include <test_resource_data.h>

using namespace monad;
using namespace monad::test;

namespace
{

    constexpr bytes4k_t make_bstore_val(uint8_t const byte)
    {
        bytes4k_t val{};
        std::fill_n(val.bytes, sizeof(val.bytes), byte);
        return val;
    }

    constexpr auto TEST_KEY1 =
        0x00000000000000000000000000000000000000000000000000000000deadbeef_bytes32;
    constexpr auto TEST_KEY2 =
        0x1111111111111111111111111111111111111111111111111111111111111111_bytes32;
    constexpr auto TEST_KEY3 =
        0x11111111111111111111111111111111111111111111111111111111111111AB_bytes32;
    constexpr auto TEST_SSTORE_VAL1 =
        0xABABABABABABABABABABABABABABABABABABABABABABABABABABABABABABABAB_bytes32;
    constexpr auto TEST_SSTORE_VAL2 =
        0xCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCD_bytes32;
    constexpr auto TEST_SSTORE_VAL3 =
        0xEFEFEFEFEFEFEFEFEFEFEFEFEFEFEFEFEFEFEFEFEFEFEFEFEFEFEFEFEFEFEFEF_bytes32;
    constexpr auto TEST_BSTORE_VAL1 = make_bstore_val(0xAB);
    constexpr auto TEST_BSTORE_VAL2 = make_bstore_val(0xCD);
    constexpr auto TEST_BSTORE_VAL3 = make_bstore_val(0xEF);

    struct InMemoryBstoreFixture : public ::testing::Test
    {
        InMemoryMachine machine;
        mpt::Db db{machine};
        TrieDb tdb{db};
        vm::VM vm;
    };

    struct OnDiskBstoreFixture : public ::testing::Test
    {
        OnDiskMachine machine;
        mpt::Db db{machine, mpt::OnDiskDbConfig{}};
        TrieDb tdb{db};
        vm::VM vm;
    };
}

enum class Prefix
{
    BYTES_STORAGE,
    BLOCK_STORAGE
};

template <typename TDB>
struct BstoreTest : public TDB
{

    std::optional<bytes32_t> storage_root(Prefix const prefix)
    {
        uint8_t const storage_prefix = (prefix == Prefix::BYTES_STORAGE)
                                           ? STORAGE_PREFIX_NIBBLE
                                           : BLOCK_STORAGE_PREFIX_NIBBLE;
        auto const res = this->db.find(
            this->tdb.get_root(),
            concat(
                FINALIZED_NIBBLE,
                STATE_NIBBLE,
                mpt::NibblesView{
                    keccak256({ADDR_A.bytes, sizeof(ADDR_A.bytes)})},
                storage_prefix),
            this->tdb.get_block_number());

        if (!res.has_value()) {
            return std::nullopt;
        }

        byte_string_view const data = res.value().node->data();
        MONAD_ASSERT(data.size() == 32);
        return unaligned_load<bytes32_t>(data.data());
    }
};

using BstoreDBTypes =
    ::testing::Types<InMemoryBstoreFixture, OnDiskBstoreFixture>;
TYPED_TEST_SUITE(BstoreTest, BstoreDBTypes);

TYPED_TEST(BstoreTest, simple)
{
    Account acct{.nonce = 1};

    commit_sequential(
        this->tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .block_storage =
                     {{TEST_KEY1, {bytes4k_t{}, TEST_BSTORE_VAL1}}},
             }}},
        Code{},
        BlockHeader{.number = 0});

    BlockState bs{this->tdb, this->vm};
    State s{bs, Incarnation{1, 1}};

    EXPECT_TRUE(s.account_exists(ADDR_A));
    EXPECT_EQ(s.get_block_storage(ADDR_A, TEST_KEY1), TEST_BSTORE_VAL1);

    // expected results generated from python reference impl
    EXPECT_FALSE(this->storage_root(Prefix::BYTES_STORAGE).has_value());
    EXPECT_EQ(
        this->storage_root(Prefix::BLOCK_STORAGE),
        0xfe076f3a573538289e5222f053b9d36d97cdbab3f747d7d883aaa43bfdaf0849_bytes32);
}

TYPED_TEST(BstoreTest, read_storage_and_block_storage)
{
    Account acct{.nonce = 1};

    commit_sequential(
        this->tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage =
                     {{TEST_KEY1, {bytes32_t{}, TEST_SSTORE_VAL1}},
                      {TEST_KEY2, {bytes32_t{}, TEST_SSTORE_VAL2}},
                      {TEST_KEY3, {bytes32_t{}, TEST_SSTORE_VAL3}}},
                 .block_storage =
                     {{TEST_KEY1, {bytes4k_t{}, TEST_BSTORE_VAL1}},
                      {TEST_KEY2, {bytes4k_t{}, TEST_BSTORE_VAL2}},
                      {TEST_KEY3, {bytes4k_t{}, TEST_BSTORE_VAL3}}}}}},
        Code{},
        BlockHeader{.number = 0});

    BlockState bs{this->tdb, this->vm};
    State s{bs, Incarnation{1, 1}};

    EXPECT_TRUE(s.account_exists(ADDR_A));
    EXPECT_EQ(s.get_storage(ADDR_A, TEST_KEY1), TEST_SSTORE_VAL1);
    EXPECT_EQ(s.get_storage(ADDR_A, TEST_KEY2), TEST_SSTORE_VAL2);
    EXPECT_EQ(s.get_storage(ADDR_A, TEST_KEY3), TEST_SSTORE_VAL3);
    EXPECT_EQ(s.get_block_storage(ADDR_A, TEST_KEY1), TEST_BSTORE_VAL1);
    EXPECT_EQ(s.get_block_storage(ADDR_A, TEST_KEY2), TEST_BSTORE_VAL2);
    EXPECT_EQ(s.get_block_storage(ADDR_A, TEST_KEY3), TEST_BSTORE_VAL3);

    // expected results generated from python reference impl
    EXPECT_EQ(
        this->storage_root(Prefix::BYTES_STORAGE),
        0x0078d2a1a662c21075661526fa04574a62c49648bf978f7706621b364ba71e6e_bytes32);
    EXPECT_EQ(
        this->storage_root(Prefix::BLOCK_STORAGE),
        0x2663a88b4ce0d80c492388ddbfee58d006cbd16b16e958247f0947c27f89bc0a_bytes32);
}
