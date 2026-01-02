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

#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/test/test_fixtures_gtest.hpp>
#include <category/vm/vm.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

using namespace monad;
using namespace monad::test;

namespace
{
    constexpr auto bstore_key1 =
        0x00000000000000000000000000000000000000000000000000000000deadbeef_bytes32;
    constexpr auto bstore_key2 =
        0x1111111111111111111111111111111111111111111111111111111111111111_bytes32;
    constexpr auto storage_key1 =
        0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
    constexpr auto storage_key2 =
        0x2222222222222222222222222222222222222222222222222222222222222222_bytes32;
    constexpr auto storage_value1 =
        0x0000000000000000000000000000000000000000000000000000000000000042_bytes32;
    constexpr auto storage_value2 =
        0x0000000000000000000000000000000000000000000000000000000000000084_bytes32;

    bytes4k_t make_bstore_value(uint8_t fill_byte)
    {
        bytes4k_t val{};
        std::memset(val.bytes, fill_byte, sizeof(val.bytes));
        return val;
    }

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

template <typename TDB>
struct BstoreTest : public TDB
{
};

using BstoreDBTypes =
    ::testing::Types<InMemoryBstoreFixture, OnDiskBstoreFixture>;
TYPED_TEST_SUITE(BstoreTest, BstoreDBTypes);

TYPED_TEST(BstoreTest, simple)
{
    Account acct{.nonce = 1};

    auto const bstore_val = make_bstore_value(0xAB);

    commit_sequential(
        this->tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage = {},
                 .block_storage = {{bstore_key1, {bytes4k_t{}, bstore_val}}}}}},
        Code{},
        BlockHeader{.number = 0});

    BlockState bs{this->tdb, this->vm};
    State s{bs, Incarnation{1, 1}};

    EXPECT_TRUE(s.account_exists(ADDR_A));
    EXPECT_EQ(s.get_block_storage(ADDR_A, bstore_key1), bstore_val);
    EXPECT_EQ(s.get_block_storage(ADDR_A, bstore_key2), bytes4k_t{});
}

TYPED_TEST(BstoreTest, read_storage_and_block_storage)
{
    Account acct{.nonce = 1};

    auto const bstore_val1 = make_bstore_value(0x11);
    auto const bstore_val2 = make_bstore_value(0x22);

    commit_sequential(
        this->tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage =
                     {{storage_key1, {bytes32_t{}, storage_value1}},
                      {storage_key2, {bytes32_t{}, storage_value2}}},
                 .block_storage =
                     {{bstore_key1, {bytes4k_t{}, bstore_val1}},
                      {bstore_key2, {bytes4k_t{}, bstore_val2}}}}}},
        Code{},
        BlockHeader{.number = 0});

    {
        BlockState bs{this->tdb, this->vm};
        State s{bs, Incarnation{1, 1}};

        EXPECT_TRUE(s.account_exists(ADDR_A));
        EXPECT_EQ(s.get_storage(ADDR_A, storage_key1), storage_value1);
        EXPECT_EQ(s.get_storage(ADDR_A, storage_key2), storage_value2);
        EXPECT_EQ(s.get_block_storage(ADDR_A, bstore_key1), bstore_val1);
        EXPECT_EQ(s.get_block_storage(ADDR_A, bstore_key2), bstore_val2);
    }

    acct = this->tdb.read_account(ADDR_A).value();
    auto const bstore_val3 = make_bstore_value(0x33);
    commit_sequential(
        this->tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {acct, acct},
                 .storage = {{storage_key1, {storage_value1, storage_value2}}},
                 .block_storage =
                     {{bstore_key1, {bstore_val1, bstore_val3}}}}}},
        Code{},
        BlockHeader{.number = 1});

    {
        BlockState bs{this->tdb, this->vm};
        State s{bs, Incarnation{1, 1}};

        EXPECT_TRUE(s.account_exists(ADDR_A));
        EXPECT_EQ(s.get_storage(ADDR_A, storage_key1), storage_value2);
        EXPECT_EQ(s.get_storage(ADDR_A, storage_key2), storage_value2);
        EXPECT_EQ(s.get_block_storage(ADDR_A, bstore_key1), bstore_val3);
        EXPECT_EQ(s.get_block_storage(ADDR_A, bstore_key2), bstore_val2);
    }
}

TYPED_TEST(BstoreTest, backwards_compatibility_no_block_storage)
{
    Account acct{.balance = 1'000'000, .nonce = 1337};

    commit_sequential(
        this->tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage =
                     {{storage_key1, {bytes32_t{}, storage_value1}},
                      {storage_key2, {bytes32_t{}, storage_value2}}}}}},
        Code{},
        BlockHeader{.number = 0});

    {
        BlockState bs{this->tdb, this->vm};
        State s{bs, Incarnation{1, 1}};

        EXPECT_TRUE(s.account_exists(ADDR_A));
        EXPECT_EQ(s.get_storage(ADDR_A, storage_key1), storage_value1);
        EXPECT_EQ(s.get_storage(ADDR_A, storage_key2), storage_value2);
        EXPECT_EQ(s.get_block_storage(ADDR_A, bstore_key1), bytes4k_t{});
    }

    acct = this->tdb.read_account(ADDR_A).value();
    commit_sequential(
        this->tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {acct, acct},
                 .storage =
                     {{storage_key1, {storage_value1, storage_value2}}}}}},
        Code{},
        BlockHeader{.number = 1});

    {
        BlockState bs{this->tdb, this->vm};
        State s{bs, Incarnation{1, 1}};

        EXPECT_TRUE(s.account_exists(ADDR_A));
        EXPECT_EQ(s.get_storage(ADDR_A, storage_key1), storage_value2);
        EXPECT_EQ(s.get_storage(ADDR_A, storage_key2), storage_value2);
        EXPECT_EQ(s.get_block_storage(ADDR_A, bstore_key1), bytes4k_t{});
    }
}

TYPED_TEST(BstoreTest, deletion)
{
    Account acct{.nonce = 1};

    auto const bstore_val1 = make_bstore_value(0xAA);
    auto const bstore_val2 = make_bstore_value(0xBB);

    commit_sequential(
        this->tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage = {},
                 .block_storage =
                     {{bstore_key1, {bytes4k_t{}, bstore_val1}},
                      {bstore_key2, {bytes4k_t{}, bstore_val2}}}}}},
        Code{},
        BlockHeader{.number = 0});

    {
        BlockState bs{this->tdb, this->vm};
        State s{bs, Incarnation{1, 1}};

        EXPECT_TRUE(s.account_exists(ADDR_A));
        EXPECT_EQ(s.get_block_storage(ADDR_A, bstore_key1), bstore_val1);
        EXPECT_EQ(s.get_block_storage(ADDR_A, bstore_key2), bstore_val2);
    }

    acct = this->tdb.read_account(ADDR_A).value();

    // delete `key1`
    commit_sequential(
        this->tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {acct, acct},
                 .storage = {},
                 .block_storage =
                     {{bstore_key1, {bstore_val1, bytes4k_t{}}}}}}},
        Code{},
        BlockHeader{.number = 1});

    {
        BlockState bs{this->tdb, this->vm};
        State s{bs, Incarnation{1, 1}};

        EXPECT_TRUE(s.account_exists(ADDR_A));
        EXPECT_EQ(s.get_block_storage(ADDR_A, bstore_key1), bytes4k_t{});
        EXPECT_EQ(s.get_block_storage(ADDR_A, bstore_key2), bstore_val2);
    }
}
