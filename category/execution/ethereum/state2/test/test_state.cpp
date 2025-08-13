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

#include <category/core/blake3.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/db_cache.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <test_resource_data.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <memory>
#include <optional>
#include <random>

using namespace monad;
using namespace monad::test;

namespace
{

    constexpr auto a = 0x5353535353535353535353535353535353535353_address;
    constexpr auto b = 0xbebebebebebebebebebebebebebebebebebebebe_address;
    constexpr auto c = 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5_address;
    constexpr auto key1 =
        0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
    constexpr auto key2 =
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
    constexpr auto key3 =
        0x5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b_bytes32;
    constexpr auto value1 =
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32;
    constexpr auto value2 =
        0x0000000000000000000000000000000000000000000000000000000000000007_bytes32;
    constexpr auto value3 =
        0x000000000000000000000000000000000000000000000000000000000000000a_bytes32;
    constexpr auto null =
        0x0000000000000000000000000000000000000000000000000000000000000000_bytes32;
    constexpr auto hash1 =
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
    constexpr auto code_hash1 =
        0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
    constexpr auto code_hash2 =
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
    constexpr auto code1 =
        byte_string{0x65, 0x74, 0x68, 0x65, 0x72, 0x6d, 0x69};
    auto const icode1 = vm::make_shared_intercode(code1);
    constexpr auto code2 =
        byte_string{0x6e, 0x65, 0x20, 0x2d, 0x20, 0x45, 0x55, 0x31, 0x34};
    auto const icode2 = vm::make_shared_intercode(code2);

    struct InMemoryTrieDbFixture : public ::testing::Test
    {
        InMemoryMachine machine;
        mpt::Db db{machine};
        TrieDb tdb{db};
        vm::VM vm;
    };

    struct OnDiskTrieDbFixture : public ::testing::Test
    {
        OnDiskMachine machine;
        mpt::Db db{machine, mpt::OnDiskDbConfig{}};
        TrieDb tdb{db};
        vm::VM vm;
    };

    struct TwoOnDisk : public ::testing::Test
    {
        OnDiskMachine machine;
        mpt::Db db1{machine, mpt::OnDiskDbConfig{.file_size_db = 8}};
        mpt::Db db2{machine, mpt::OnDiskDbConfig{.file_size_db = 8}};
        TrieDb tdb1{db1};
        TrieDb tdb2{db2};
        vm::VM vm;
    };
}

template <typename TDB>
struct StateTest : public TDB
{
};

using DBTypes = ::testing::Types<InMemoryTrieDbFixture, OnDiskTrieDbFixture>;
TYPED_TEST_SUITE(StateTest, DBTypes);

TYPED_TEST(StateTest, access_account)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 10'000}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};

    EXPECT_EQ(s.access_account(a), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_account(a), EVMC_ACCESS_WARM);
    EXPECT_EQ(s.access_account(b), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_account(b), EVMC_ACCESS_WARM);
}

TYPED_TEST(StateTest, account_exists)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 10'000}}}}},
        Code{},
        BlockHeader{});

    EXPECT_TRUE(this->tdb.read_account(a).has_value());

    State s{bs, Incarnation{1, 1}};

    EXPECT_TRUE(s.account_exists(a));
    EXPECT_FALSE(s.account_exists(b));
}

TYPED_TEST(StateTest, create_contract)
{
    BlockState bs{this->tdb, this->vm};

    State s{bs, Incarnation{1, 1}};
    s.create_contract(a);
    EXPECT_TRUE(s.account_exists(a));

    // allow pre-existing empty account
    EXPECT_FALSE(s.account_exists(b));
    s.create_contract(b);
    EXPECT_TRUE(s.account_exists(b));
}

TYPED_TEST(StateTest, get_balance)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 10'000}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};

    EXPECT_EQ(s.get_balance(a), bytes32_t{10'000});
    EXPECT_EQ(s.get_balance(b), bytes32_t{0});
    EXPECT_EQ(s.get_balance(c), bytes32_t{0});
}

TYPED_TEST(StateTest, add_to_balance)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, Account{.balance = 1}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};
    s.add_to_balance(a, 10'000);
    s.add_to_balance(b, 20'000);

    EXPECT_EQ(s.get_balance(a), bytes32_t{10'001});
    EXPECT_EQ(s.get_balance(b), bytes32_t{20'000});
}

TYPED_TEST(StateTest, get_nonce)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, Account{.nonce = 2}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};

    EXPECT_EQ(s.get_nonce(a), 2);
    EXPECT_EQ(s.get_nonce(b), 0);
    EXPECT_EQ(s.get_nonce(c), 0);
}

TYPED_TEST(StateTest, set_nonce)
{
    BlockState bs{this->tdb, this->vm};

    State s{bs, Incarnation{1, 1}};
    s.set_nonce(b, 1);

    EXPECT_EQ(s.get_nonce(b), 1);
}

TYPED_TEST(StateTest, get_code_hash)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.code_hash = hash1}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};

    EXPECT_EQ(s.get_code_hash(a), hash1);
    EXPECT_EQ(s.get_code_hash(b), NULL_HASH);
    EXPECT_EQ(s.get_code_hash(c), NULL_HASH);
}

TYPED_TEST(StateTest, set_code_hash)
{
    BlockState bs{this->tdb, this->vm};

    State s{bs, Incarnation{1, 1}};
    s.create_contract(b);
    s.set_code_hash(b, hash1);

    EXPECT_EQ(s.get_code_hash(b), hash1);
}

TYPED_TEST(StateTest, selfdestruct)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{.account = {std::nullopt, Account{.balance = 18'000}}}},
            {c,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 38'000}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};
    s.create_contract(b);
    s.add_to_balance(b, 28'000);

    EXPECT_TRUE(s.selfdestruct<EVMC_SHANGHAI>(a, c));
    EXPECT_EQ(s.get_balance(a), bytes32_t{});
    EXPECT_EQ(s.get_balance(c), bytes32_t{56'000});
    EXPECT_FALSE(s.selfdestruct<EVMC_SHANGHAI>(a, c));

    EXPECT_TRUE(s.selfdestruct<EVMC_SHANGHAI>(b, c));
    EXPECT_EQ(s.get_balance(b), bytes32_t{});
    EXPECT_EQ(s.get_balance(c), bytes32_t{84'000});
    EXPECT_FALSE(s.selfdestruct<EVMC_SHANGHAI>(b, c));

    s.destruct_suicides<EVMC_SHANGHAI>();
    EXPECT_FALSE(s.account_exists(a));
    EXPECT_FALSE(s.account_exists(b));
}

TYPED_TEST(StateTest, selfdestruct_cancun_separate_tx)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 18'000,
                          .incarnation = Incarnation{1, 1}}}}},
            {c,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 38'000,
                          .incarnation = Incarnation{1, 1}}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 2}};

    EXPECT_TRUE(s.selfdestruct<EVMC_CANCUN>(a, c));
    EXPECT_EQ(s.get_balance(a), bytes32_t{});
    EXPECT_EQ(s.get_balance(c), bytes32_t{56'000});
    EXPECT_FALSE(s.selfdestruct<EVMC_CANCUN>(a, c));

    s.destruct_suicides<EVMC_CANCUN>();
    EXPECT_TRUE(s.account_exists(a));
}

TYPED_TEST(StateTest, selfdestruct_cancun_same_tx)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 18'000,
                          .incarnation = Incarnation{1, 1}}}}},
            {c,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 38'000,
                          .incarnation = Incarnation{1, 1}}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};

    EXPECT_TRUE(s.selfdestruct<EVMC_CANCUN>(a, c));
    EXPECT_EQ(s.get_balance(a), bytes32_t{});
    EXPECT_EQ(s.get_balance(c), bytes32_t{56'000});
    EXPECT_FALSE(s.selfdestruct<EVMC_CANCUN>(a, c));

    s.destruct_suicides<EVMC_CANCUN>();
    EXPECT_FALSE(s.account_exists(a));
}

TYPED_TEST(StateTest, selfdestruct_self_separate_tx)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 18'000}}}}},
        Code{},
        BlockHeader{});

    {
        // Pre-cancun behavior
        State s{bs, Incarnation{1, 1}};

        EXPECT_TRUE(s.selfdestruct<EVMC_SHANGHAI>(a, a));
        EXPECT_EQ(s.get_balance(a), bytes32_t{});

        s.destruct_suicides<EVMC_SHANGHAI>();
        EXPECT_FALSE(s.account_exists(a));
    }
    {
        // Post-cancun behavior
        State s{bs, Incarnation{1, 1}};

        EXPECT_TRUE(s.selfdestruct<EVMC_CANCUN>(a, a));
        EXPECT_EQ(s.get_balance(a), bytes32_t{18'000}); // no ether burned

        s.destruct_suicides<EVMC_CANCUN>();
        EXPECT_TRUE(s.account_exists(a));
    }
}

TYPED_TEST(StateTest, selfdestruct_self_same_tx)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 18'000,
                          .incarnation = Incarnation{1, 1}}}}}},
        Code{},
        BlockHeader{});

    auto run = [&]<evmc_revision rev>() {
        State s{bs, Incarnation{1, 1}};

        EXPECT_TRUE(s.selfdestruct<rev>(a, a));
        EXPECT_EQ(s.get_balance(a), bytes32_t{});

        s.destruct_suicides<rev>();
        EXPECT_FALSE(s.account_exists(a));
    };
    // Behavior doesn't change in cancun if in same txn
    run.template operator()<EVMC_SHANGHAI>();
    run.template operator()<EVMC_CANCUN>();
}

TYPED_TEST(StateTest, selfdestruct_merge_incarnation)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 18'000}},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{},
        BlockHeader{});
    {
        State s1{bs, Incarnation{1, 1}};

        s1.selfdestruct<EVMC_SHANGHAI>(a, a);
        s1.destruct_suicides<EVMC_SHANGHAI>();

        EXPECT_TRUE(bs.can_merge(s1));
        bs.merge(s1);
    }
    {
        State s2{bs, Incarnation{1, 2}};
        EXPECT_FALSE(s2.account_exists(a));
        s2.create_contract(a);
        EXPECT_EQ(s2.get_storage(a, key1), bytes32_t{});
    }
}

TYPED_TEST(StateTest, selfdestruct_merge_create_incarnation)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 18'000}},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{},
        BlockHeader{});
    {
        State s1{bs, Incarnation{1, 1}};

        s1.selfdestruct<EVMC_SHANGHAI>(a, b);
        s1.destruct_suicides<EVMC_SHANGHAI>();

        EXPECT_TRUE(bs.can_merge(s1));
        bs.merge(s1);
    }
    {
        State s2{bs, Incarnation{1, 2}};
        EXPECT_FALSE(s2.account_exists(a));
        s2.create_contract(a);
        EXPECT_EQ(s2.get_storage(a, key1), bytes32_t{});

        s2.set_storage(a, key1, value2);
        s2.set_storage(a, key2, value1);

        EXPECT_EQ(s2.get_storage(a, key1), value2);
        EXPECT_EQ(s2.get_storage(a, key2), value1);

        EXPECT_TRUE(bs.can_merge(s2));
        bs.merge(s2);
    }
    {
        State s3{bs, Incarnation{1, 3}};
        EXPECT_TRUE(s3.account_exists(a));
        EXPECT_EQ(s3.get_storage(a, key1), value2);
        EXPECT_EQ(s3.get_storage(a, key2), value1);
    }
}

TYPED_TEST(StateTest, selfdestruct_merge_commit_incarnation)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 18'000}},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{},
        BlockHeader{});
    {
        State s1{bs, Incarnation{1, 1}};

        s1.selfdestruct<EVMC_SHANGHAI>(a, a);
        s1.destruct_suicides<EVMC_SHANGHAI>();

        EXPECT_TRUE(bs.can_merge(s1));
        bs.merge(s1);
    }
    {
        State s2{bs, Incarnation{1, 2}};
        s2.create_contract(a);
        bs.merge(s2);
    }
    {
        bs.commit(
            bytes32_t{1},
            BlockHeader{.number = 1},
            {},
            {},
            {},
            {},
            {},
            std::nullopt);
        this->tdb.finalize(1, bytes32_t{1});
        this->tdb.set_block_and_prefix(1);
        EXPECT_EQ(
            this->tdb.read_storage(a, Incarnation{1, 2}, key1), bytes32_t{});
    }
}

TYPED_TEST(StateTest, selfdestruct_merge_create_commit_incarnation)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage =
                     {{key1, {bytes32_t{}, value2}},
                      {key3, {bytes32_t{}, value3}}}}}},
        Code{},
        BlockHeader{});
    {
        State s1{bs, Incarnation{1, 1}};

        s1.selfdestruct<EVMC_SHANGHAI>(a, a);
        s1.destruct_suicides<EVMC_SHANGHAI>();

        EXPECT_TRUE(bs.can_merge(s1));
        bs.merge(s1);
    }
    {
        State s2{bs, Incarnation{1, 2}};
        s2.add_to_balance(a, 1000);

        s2.set_storage(a, key1, value1);
        s2.set_storage(a, key2, value2);

        EXPECT_TRUE(bs.can_merge(s2));
        bs.merge(s2);
    }
    {
        bs.commit(
            bytes32_t{1},
            BlockHeader{.number = 1},
            {},
            {},
            {},
            {},
            {},
            std::nullopt);
        this->tdb.finalize(1, bytes32_t{1});
        this->tdb.set_block_and_prefix(1);
        EXPECT_EQ(this->tdb.read_storage(a, Incarnation{1, 2}, key1), value1);
        EXPECT_EQ(this->tdb.read_storage(a, Incarnation{1, 2}, key2), value2);
        EXPECT_EQ(
            this->tdb.state_root(),
            0x5B853ED6066181BF0E0D405DA0926FD7707446BCBE670DE13C9EDA7A84F6A401_bytes32);
    }
}

TYPED_TEST(StateTest, selfdestruct_create_destroy_create_commit_incarnation)
{
    BlockState bs{this->tdb, this->vm};
    {
        State s1{bs, Incarnation{1, 1}};

        s1.create_contract(a);
        s1.set_storage(a, key1, value1);
        s1.selfdestruct<EVMC_SHANGHAI>(a, b);
        s1.destruct_suicides<EVMC_SHANGHAI>();

        EXPECT_TRUE(bs.can_merge(s1));
        bs.merge(s1);
    }
    {
        State s2{bs, Incarnation{1, 2}};
        s2.create_contract(a);

        s2.set_storage(a, key2, value3);

        EXPECT_TRUE(bs.can_merge(s2));
        bs.merge(s2);
    }
    {
        bs.commit(
            NULL_HASH_BLAKE3,
            BlockHeader{.number = 0},
            {},
            {},
            {},
            {},
            {},
            std::nullopt);
        this->tdb.finalize(0, NULL_HASH_BLAKE3);
        this->tdb.set_block_and_prefix(0);
        EXPECT_EQ(
            this->tdb.read_storage(a, Incarnation{1, 2}, key1), bytes32_t{});
        EXPECT_EQ(this->tdb.read_storage(a, Incarnation{1, 2}, key2), value3);
    }
}

TYPED_TEST(StateTest, create_conflict_address_incarnation)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 18'000}},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{},
        BlockHeader{});

    State s1{bs, Incarnation{1, 1}};

    s1.create_contract(a);
    s1.set_storage(a, key2, value2);

    EXPECT_EQ(s1.get_storage(a, key1), bytes32_t{});
    EXPECT_EQ(s1.get_storage(a, key2), value2);
}

TYPED_TEST(StateTest, destruct_touched_dead)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{.account = {std::nullopt, Account{.balance = 10'000}}}},
            {b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};
    EXPECT_TRUE(s.account_exists(a));
    s.destruct_touched_dead();
    s.destruct_suicides<EVMC_SHANGHAI>();
    EXPECT_TRUE(s.account_exists(a));
    EXPECT_TRUE(s.account_exists(b));

    s.subtract_from_balance(a, 10'000);
    s.destruct_touched_dead();
    s.destruct_suicides<EVMC_SHANGHAI>();

    EXPECT_FALSE(s.account_exists(a));
    EXPECT_TRUE(s.account_exists(b));

    s.touch(b);
    s.destruct_touched_dead();
    s.destruct_suicides<EVMC_SHANGHAI>();
    EXPECT_FALSE(s.account_exists(b));

    s.add_to_balance(a, 0);
    EXPECT_TRUE(s.account_exists(a));
    s.destruct_touched_dead();
    s.destruct_suicides<EVMC_SHANGHAI>();
    EXPECT_FALSE(s.account_exists(a));

    s.subtract_from_balance(a, 0);
    EXPECT_TRUE(s.account_exists(a));
    s.destruct_touched_dead();
    s.destruct_suicides<EVMC_SHANGHAI>();
    EXPECT_FALSE(s.account_exists(a));
}

// Storage
TYPED_TEST(StateTest, access_storage)
{
    BlockState bs{this->tdb, this->vm};

    State s{bs, Incarnation{1, 1}};
    EXPECT_EQ(s.access_storage(a, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(a, key1), EVMC_ACCESS_WARM);
    EXPECT_EQ(s.access_storage(b, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(b, key1), EVMC_ACCESS_WARM);
    EXPECT_EQ(s.access_storage(a, key2), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(a, key2), EVMC_ACCESS_WARM);
    EXPECT_EQ(s.access_storage(b, key2), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(b, key2), EVMC_ACCESS_WARM);
}

TYPED_TEST(StateTest, get_storage)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}},
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};
    EXPECT_TRUE(s.account_exists(a));
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_EQ(s.get_storage(a, key1), value1);
    EXPECT_EQ(s.get_storage(a, key2), value2);
    EXPECT_EQ(s.get_storage(a, key3), null);
    EXPECT_EQ(s.get_storage(b, key1), value1);
    EXPECT_EQ(s.get_storage(b, key2), null);
    EXPECT_EQ(s.get_storage(b, key3), null);
}

TYPED_TEST(StateTest, set_storage_modified)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key2, {bytes32_t{}, value2}}}}},
            {b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};
    EXPECT_TRUE(s.account_exists(a));
    EXPECT_EQ(s.set_storage(a, key2, value3), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.get_storage(a, key2), value3);
}

TYPED_TEST(StateTest, set_storage_deleted)
{
    BlockState bs{this->tdb, this->vm};

    commit_sequential(
        this->tdb,
        StateDeltas{
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_EQ(s.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(s.get_storage(b, key1), null);
    EXPECT_EQ(s.set_storage(b, key1, null), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.get_storage(b, key1), null);
    EXPECT_EQ(s.set_storage(b, key1, value2), EVMC_STORAGE_DELETED_ADDED);
    EXPECT_EQ(s.get_storage(b, key1), value2);
}

TYPED_TEST(StateTest, set_storage_added)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{{b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_EQ(s.set_storage(b, key1, value1), EVMC_STORAGE_ADDED);
    EXPECT_EQ(s.get_storage(b, key1), value1);
    EXPECT_EQ(s.set_storage(b, key1, value1), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.get_storage(b, key1), value1);
    EXPECT_EQ(s.set_storage(b, key1, value2), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.get_storage(b, key1), value2);
}

TYPED_TEST(StateTest, set_storage_different_assigned)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key2, {bytes32_t{}, value2}}}}},
            {b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};
    EXPECT_TRUE(s.account_exists(a));
    EXPECT_EQ(s.set_storage(a, key2, value3), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.get_storage(a, key2), value3);
    EXPECT_EQ(s.set_storage(a, key2, value1), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.get_storage(a, key2), value1);
}

TYPED_TEST(StateTest, set_storage_unchanged_assigned)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key2, {bytes32_t{}, value2}}}}},
            {b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};
    EXPECT_TRUE(s.account_exists(a));
    EXPECT_EQ(s.set_storage(a, key2, value2), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.get_storage(a, key2), value2);
}

TYPED_TEST(StateTest, set_storage_added_deleted)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{{b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_EQ(s.set_storage(b, key1, value1), EVMC_STORAGE_ADDED);
    EXPECT_EQ(s.get_storage(b, key1), value1);
    EXPECT_EQ(s.set_storage(b, key1, null), EVMC_STORAGE_ADDED_DELETED);
    EXPECT_EQ(s.get_storage(b, key1), null);
}

TYPED_TEST(StateTest, set_storage_added_deleted_null)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{{b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_EQ(s.set_storage(b, key1, null), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.get_storage(b, key1), null);
    EXPECT_EQ(s.set_storage(b, key1, null), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.get_storage(b, key1), null);
}

TYPED_TEST(StateTest, set_storage_modify_delete)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key2, {bytes32_t{}, value2}}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_EQ(s.set_storage(b, key2, value1), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.get_storage(b, key2), value1);
    EXPECT_EQ(s.set_storage(b, key2, null), EVMC_STORAGE_MODIFIED_DELETED);
    EXPECT_EQ(s.get_storage(b, key2), null);
}

TYPED_TEST(StateTest, set_storage_delete_restored)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key2, {bytes32_t{}, value2}}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_EQ(s.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(s.get_storage(b, key2), null);
    EXPECT_EQ(s.set_storage(b, key2, value2), EVMC_STORAGE_DELETED_RESTORED);
    EXPECT_EQ(s.get_storage(b, key2), value2);
}

TYPED_TEST(StateTest, set_storage_modified_restored)
{
    BlockState bs{this->tdb, this->vm};
    commit_sequential(
        this->tdb,
        StateDeltas{
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key2, {bytes32_t{}, value2}}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_EQ(s.set_storage(b, key2, value1), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.get_storage(b, key2), value1);
    EXPECT_EQ(s.set_storage(b, key2, value2), EVMC_STORAGE_MODIFIED_RESTORED);
    EXPECT_EQ(s.get_storage(b, key2), value2);
}

// Code
TYPED_TEST(StateTest, get_code_size)
{
    BlockState bs{this->tdb, this->vm};
    Account acct{.code_hash = code_hash1};
    commit_sequential(
        this->tdb,
        StateDeltas{{a, StateDelta{.account = {std::nullopt, acct}}}},
        Code{{code_hash1, icode1}},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};
    EXPECT_EQ(s.get_code_size(a), code1.size());
}

TYPED_TEST(StateTest, copy_code)
{
    BlockState bs{this->tdb, this->vm};
    Account acct_a{.code_hash = code_hash1};
    Account acct_b{.code_hash = code_hash2};

    commit_sequential(
        this->tdb,
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, acct_a}}},
            {b, StateDelta{.account = {std::nullopt, acct_b}}}},
        Code{{code_hash1, icode1}, {code_hash2, icode2}},
        BlockHeader{});

    static constexpr unsigned size{8};
    uint8_t buffer[size];

    State s{bs, Incarnation{1, 1}};

    { // underflow
        auto const total = s.copy_code(a, 0u, buffer, size);
        EXPECT_EQ(total, code1.size());
        EXPECT_EQ(0, std::memcmp(buffer, code1.c_str(), total));
    }
    { // offset
        static constexpr auto offset = 2u;
        static constexpr auto to_copy = 3u;
        auto const offset_total = s.copy_code(a, offset, buffer, to_copy);
        EXPECT_EQ(offset_total, to_copy);
        EXPECT_EQ(0, std::memcmp(buffer, code1.c_str() + offset, offset_total));
    }
    { // offset overflow
        static constexpr auto offset = 4u;
        auto const offset_total = s.copy_code(a, offset, buffer, size);
        EXPECT_EQ(offset_total, 3u);
        EXPECT_EQ(0, std::memcmp(buffer, code1.c_str() + offset, offset_total));
    }
    { // regular overflow
        auto const total = s.copy_code(b, 0u, buffer, size);
        EXPECT_EQ(total, size);
        EXPECT_EQ(0, std::memcmp(buffer, code2.c_str(), total));
    }
    { // empty account
        auto const total = s.copy_code(c, 0u, buffer, size);
        EXPECT_EQ(total, 0u);
    }
    { // offset outside size
        auto const total = s.copy_code(a, 9, buffer, size);
        EXPECT_EQ(total, 0);
    }
}

TYPED_TEST(StateTest, get_code)
{
    byte_string const contract{0x60, 0x34, 0x00};

    BlockState bs{this->tdb, this->vm};

    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.code_hash = code_hash1}}}}},
        Code{{code_hash1, vm::make_shared_intercode(contract)}},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};

    {
        s.access_account(a);
        auto const c = s.get_code(a)->intercode();
        EXPECT_EQ(byte_string_view(c->code(), c->code_size()), contract);
    }
    { // non-existant account
        auto const c = s.get_code(b)->intercode();
        EXPECT_EQ(byte_string_view(c->code(), c->code_size()), byte_string{});
    }
}

TYPED_TEST(StateTest, set_code)
{
    BlockState bs{this->tdb, this->vm};

    State s{bs, Incarnation{1, 1}};
    s.create_contract(a);
    s.create_contract(b);
    s.set_code(a, code2);
    s.set_code(b, byte_string{});

    auto const a_icode = s.get_code(a)->intercode();
    EXPECT_EQ(byte_string_view(a_icode->code(), a_icode->code_size()), code2);
    auto const b_icode = s.get_code(b)->intercode();
    EXPECT_EQ(
        byte_string_view(b_icode->code(), b_icode->code_size()), byte_string{});
}

TYPED_TEST(StateTest, can_merge_same_account_different_storage)
{
    BlockState bs{this->tdb, this->vm};

    commit_sequential(
        this->tdb,
        StateDeltas{
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 40'000}},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}},
            {c,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 50'000}},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}}},
        Code{},
        BlockHeader{});

    State as{bs, Incarnation{1, 1}};
    EXPECT_TRUE(as.account_exists(b));
    EXPECT_EQ(as.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
    EXPECT_TRUE(bs.can_merge(as));
    bs.merge(as);

    State cs{bs, Incarnation{1, 2}};
    EXPECT_TRUE(cs.account_exists(b));
    EXPECT_EQ(cs.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_TRUE(bs.can_merge(cs));
    bs.merge(cs);
}

TYPED_TEST(StateTest, cant_merge_colliding_storage)
{
    BlockState bs{this->tdb, this->vm};

    commit_sequential(
        this->tdb,
        StateDeltas{
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 40'000}},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{},
        BlockHeader{});

    State as{bs, Incarnation{1, 1}};
    EXPECT_TRUE(as.account_exists(b));
    EXPECT_EQ(as.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);

    State cs{bs, Incarnation{1, 2}};
    EXPECT_TRUE(cs.account_exists(b));
    EXPECT_EQ(cs.set_storage(b, key1, null), EVMC_STORAGE_DELETED);

    EXPECT_TRUE(bs.can_merge(as));
    bs.merge(as);
    EXPECT_FALSE(bs.can_merge(cs));

    // Need to rerun txn 1 - get new changset
    {
        State cs{bs, Incarnation{1, 2}};
        EXPECT_TRUE(cs.account_exists(b));
        EXPECT_EQ(cs.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_TRUE(bs.can_merge(cs));
        bs.merge(cs);
    }
}

TYPED_TEST(StateTest, merge_txn0_and_txn1)
{
    BlockState bs{this->tdb, this->vm};

    commit_sequential(
        this->tdb,
        StateDeltas{
            {a,
             StateDelta{.account = {std::nullopt, Account{.balance = 30'000}}}},
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 40'000}},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}},
            {c,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 50'000}},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}}},
        Code{},
        BlockHeader{});

    State as{bs, Incarnation{1, 1}};
    EXPECT_TRUE(as.account_exists(b));
    EXPECT_EQ(as.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(as.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(as.set_storage(b, key2, value2), EVMC_STORAGE_DELETED_RESTORED);
    EXPECT_TRUE(bs.can_merge(as));
    bs.merge(as);

    State cs{bs, Incarnation{1, 2}};
    EXPECT_TRUE(cs.account_exists(c));
    EXPECT_EQ(cs.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(cs.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_TRUE(cs.selfdestruct<EVMC_SHANGHAI>(c, a));
    cs.destruct_suicides<EVMC_SHANGHAI>();
    EXPECT_TRUE(bs.can_merge(cs));
    bs.merge(cs);
}

TYPED_TEST(StateTest, commit_storage_and_account_together_regression)
{
    BlockState bs{this->tdb, this->vm};
    State as{bs, Incarnation{1, 1}};

    as.create_contract(a);
    as.add_to_balance(a, 1);
    as.set_storage(a, key1, value1);

    bs.merge(as);
    bs.commit(
        NULL_HASH_BLAKE3,
        BlockHeader{.number = 0},
        {},
        {},
        {},
        {},
        {},
        std::nullopt);
    this->tdb.finalize(0, NULL_HASH_BLAKE3);
    this->tdb.set_block_and_prefix(0);

    EXPECT_TRUE(this->tdb.read_account(a).has_value());
    EXPECT_EQ(this->tdb.read_account(a).value().balance, 1u);
    EXPECT_EQ(this->tdb.read_storage(a, Incarnation{1, 1}, key1), value1);
}

TYPED_TEST(StateTest, set_and_then_clear_storage_in_same_commit)
{
    using namespace intx;
    BlockState bs{this->tdb, this->vm};
    State as{bs, Incarnation{1, 1}};

    as.create_contract(a);
    EXPECT_EQ(as.set_storage(a, key1, value1), EVMC_STORAGE_ADDED);
    EXPECT_EQ(as.set_storage(a, key1, null), EVMC_STORAGE_ADDED_DELETED);
    bs.merge(as);
    bs.commit(NULL_HASH_BLAKE3, {}, {}, {}, {}, {}, {}, std::nullopt);

    EXPECT_EQ(
        this->tdb.read_storage(a, Incarnation{1, 1}, key1), monad::bytes32_t{});
}

TYPED_TEST(StateTest, commit_twice)
{
    load_header(this->db, BlockHeader{.number = 8});

    // commit to Block 9 Finalized
    this->tdb.set_block_and_prefix(8);
    this->tdb.commit(
        StateDeltas{
            {a,
             StateDelta{.account = {std::nullopt, Account{.balance = 30'000}}}},
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 40'000}},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}},
            {c,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 50'000}},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}}},
        Code{},
        bytes32_t{9},
        BlockHeader{.number = 9});
    this->tdb.finalize(9, bytes32_t{9});

    { // Commit to Block 10 Round 5, on top of block 9 finalized
        this->tdb.set_block_and_prefix(9);
        BlockState bs{this->tdb, this->vm};
        State as{bs, Incarnation{1, 1}};
        EXPECT_TRUE(as.account_exists(b));
        as.add_to_balance(b, 42'000);
        as.set_nonce(b, 3);
        EXPECT_EQ(as.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(as.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(
            as.set_storage(b, key2, value2), EVMC_STORAGE_DELETED_RESTORED);
        EXPECT_TRUE(bs.can_merge(as));
        bs.merge(as);
        bs.commit(
            bytes32_t{10}, BlockHeader{.number = 10}, {}, {}, {}, {}, {}, {});
        this->tdb.finalize(10, bytes32_t{10});

        EXPECT_EQ(this->tdb.read_storage(b, Incarnation{1, 1}, key1), value2);
        EXPECT_EQ(this->tdb.read_storage(b, Incarnation{1, 1}, key2), value2);

        this->tdb.set_block_and_prefix(10, bytes32_t{10});
    }
    { // Commit to Block 11 Round 6, on top of block 10 round 5
        BlockState bs{this->tdb, this->vm};
        State cs{bs, Incarnation{2, 1}};
        EXPECT_TRUE(cs.account_exists(a));
        EXPECT_TRUE(cs.account_exists(c));
        EXPECT_EQ(cs.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(cs.set_storage(c, key2, value1), EVMC_STORAGE_MODIFIED);
        EXPECT_TRUE(cs.selfdestruct<EVMC_SHANGHAI>(c, a));
        cs.destruct_suicides<EVMC_SHANGHAI>();
        EXPECT_TRUE(bs.can_merge(cs));
        bs.merge(cs);
        bs.commit(
            bytes32_t{11}, BlockHeader{.number = 11}, {}, {}, {}, {}, {}, {});
        EXPECT_EQ(
            this->tdb.read_storage(c, Incarnation{2, 1}, key1),
            monad::bytes32_t{});
        EXPECT_EQ(
            this->tdb.read_storage(c, Incarnation{2, 1}, key2),
            monad::bytes32_t{});

        // verify finalized state is the same as round 6
        this->tdb.finalize(11, bytes32_t{11});
        this->tdb.set_block_and_prefix(11);
        EXPECT_EQ(
            this->tdb.read_storage(c, Incarnation{2, 1}, key1),
            monad::bytes32_t{});
        EXPECT_EQ(
            this->tdb.read_storage(c, Incarnation{2, 1}, key2),
            monad::bytes32_t{});
    }
}

TEST_F(OnDiskTrieDbFixture, commit_multiple_proposals)
{
    load_header(this->db, BlockHeader{.number = 9});

    // commit to block 10, round 5
    this->tdb.set_block_and_prefix(9);
    this->tdb.commit(
        StateDeltas{
            {a,
             StateDelta{.account = {std::nullopt, Account{.balance = 30'000}}}},
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 40'000}},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}},
            {c,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 50'000}},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}}},
        Code{},
        bytes32_t{10},
        BlockHeader{.number = 10},
        {},
        {},
        {},
        {});
    {
        // set to block 10 round 5
        this->tdb.set_block_and_prefix(10, bytes32_t{10});
        BlockState bs{this->tdb, this->vm};
        State as{bs, Incarnation{1, 1}};
        EXPECT_TRUE(as.account_exists(b));
        as.add_to_balance(b, 42'000);
        as.set_nonce(b, 3);
        EXPECT_EQ(as.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(as.set_storage(b, key2, null), EVMC_STORAGE_DELETED);

        EXPECT_TRUE(bs.can_merge(as));
        bs.merge(as);
        // Commit block 11 round 8 on top of block 10 round 5
        bs.commit(
            bytes32_t{118}, BlockHeader{.number = 11}, {}, {}, {}, {}, {}, {});

        EXPECT_EQ(this->tdb.read_account(b).value().balance, 82'000);
        EXPECT_EQ(this->tdb.read_storage(b, Incarnation{1, 1}, key1), value2);
        EXPECT_EQ(
            this->tdb.read_storage(b, Incarnation{1, 1}, key2), bytes32_t{});
    }
    auto const state_root_round8 = this->tdb.state_root();

    {
        // set to block 10 round 5
        this->tdb.set_block_and_prefix(10, bytes32_t{10});
        BlockState bs{this->tdb, this->vm};
        State as{bs, Incarnation{1, 1}};
        EXPECT_TRUE(as.account_exists(b));
        as.add_to_balance(b, 44'000);
        as.set_nonce(b, 3);
        EXPECT_EQ(as.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(as.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_TRUE(bs.can_merge(as));
        bs.merge(as);
        // Commit block 11 round 6 on top of block 10 round 5
        bs.commit(
            bytes32_t{116}, BlockHeader{.number = 11}, {}, {}, {}, {}, {}, {});

        EXPECT_EQ(this->tdb.read_account(b).value().balance, 84'000);
        EXPECT_EQ(
            this->tdb.read_storage(b, Incarnation{1, 1}, key1), bytes32_t{});
        EXPECT_EQ(
            this->tdb.read_storage(b, Incarnation{1, 1}, key2), bytes32_t{});
    }

    auto const state_root_round6 = this->tdb.state_root();
    {
        // set to block 10 round 5
        this->tdb.set_block_and_prefix(10, bytes32_t{10});
        BlockState bs{this->tdb, this->vm};
        State as{bs, Incarnation{1, 1}};
        EXPECT_TRUE(as.account_exists(b));
        as.add_to_balance(b, 32'000);
        as.set_nonce(b, 3);
        EXPECT_EQ(as.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(as.set_storage(b, key2, value3), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(as.set_storage(b, key1, value2), EVMC_STORAGE_DELETED_ADDED);
        EXPECT_TRUE(bs.can_merge(as));
        bs.merge(as);
        // Commit block 11 round 7 on top of block 10 round 5
        bs.commit(
            bytes32_t{117}, BlockHeader{.number = 11}, {}, {}, {}, {}, {}, {});

        EXPECT_EQ(this->tdb.read_account(b).value().balance, 72'000);
        EXPECT_EQ(this->tdb.read_storage(b, Incarnation{1, 1}, key1), value2);
        EXPECT_EQ(this->tdb.read_storage(b, Incarnation{1, 1}, key2), value3);
    }
    auto const state_root_round7 = this->tdb.state_root();
    this->tdb.finalize(11, bytes32_t{117});
    this->tdb.set_block_and_prefix(11, bytes32_t{117}); // set to block 11
    EXPECT_EQ(state_root_round7, this->tdb.state_root());

    // check state root of previous rounds
    this->tdb.set_block_and_prefix(11, bytes32_t{116});
    EXPECT_EQ(state_root_round6, this->tdb.state_root());

    this->tdb.set_block_and_prefix(11, bytes32_t{118});
    EXPECT_EQ(state_root_round8, this->tdb.state_root());
}

TEST_F(OnDiskTrieDbFixture, proposal_basics)
{
    load_header(this->db, BlockHeader{.number = 9});
    Db &db = this->tdb;
    db.set_block_and_prefix(9);
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 30'000}}}}},
        Code{},
        bytes32_t{10},
        BlockHeader{.number = 10});
    db.set_block_and_prefix(10, bytes32_t{10});
    EXPECT_EQ(db.read_account(a).value().balance, 30'000);

    DbCache db_cache(db);
    db_cache.set_block_and_prefix(10, bytes32_t{10});
    BlockState bs1(db_cache, this->vm);
    EXPECT_EQ(bs1.read_account(a).value().balance, 30'000);
    bs1.commit(bytes32_t{11}, BlockHeader{.number = 11});
    db_cache.finalize(11, bytes32_t{11});

    db_cache.set_block_and_prefix(11, bytes32_t{11});
    BlockState bs2(db_cache, this->vm);
    State as{bs2, Incarnation{1, 1}};
    EXPECT_TRUE(as.account_exists(a));
    as.add_to_balance(a, 10'000);
    EXPECT_TRUE(bs2.can_merge(as));
    bs2.merge(as);
    EXPECT_EQ(db_cache.read_account(a).value().balance, 30'000);
    bs2.commit(bytes32_t{12}, BlockHeader{.number = 12});
    EXPECT_EQ(db_cache.read_account(a).value().balance, 40'000);
    db_cache.finalize(12, bytes32_t{12});
    EXPECT_EQ(db_cache.read_account(a).value().balance, 40'000);
}

TEST_F(OnDiskTrieDbFixture, undecided_proposals)
{
    load_header(this->db, BlockHeader{.number = 9});
    DbCache db_cache(this->tdb);

    // b10 r100        a 10   b 20 v1 v2   c 30 v1 v2
    // b11 r111 r100           +40 v2 --
    // b12 r121 r111                        +10    v1
    // b11 r112 r100    +20        --           --
    // b12 r122 r112           +20 v3
    // b13 r131 r121    +30    +20    v1        v2 __
    // b13 r132 r122                  --        v3
    // b11 r113 r100    +70    +70 v3 v3    +70 v3 v3
    // finalize r111 r121 r131

    LOG_INFO("block 10 round 100");
    // b10 r100        a 10   b 20 v1 v2   c 30 v1 v2
    std::unique_ptr<StateDeltas> state_deltas{new StateDeltas{
        {a, StateDelta{.account = {std::nullopt, Account{.balance = 10'000}}}},
        {b,
         StateDelta{
             .account = {std::nullopt, Account{.balance = 20'000}},
             .storage =
                 {{key1, {bytes32_t{}, value1}},
                  {key2, {bytes32_t{}, value2}}}}},
        {c,
         StateDelta{
             .account = {std::nullopt, Account{.balance = 30'000}},
             .storage = {
                 {key1, {bytes32_t{}, value1}},
                 {key2, {bytes32_t{}, value2}}}}}}};
    Code code;
    db_cache.set_block_and_prefix(9);
    db_cache.commit(
        std::move(state_deltas),
        code,
        bytes32_t{10},
        BlockHeader{.number = 10});
    db_cache.finalize(10, bytes32_t{10});
    EXPECT_TRUE(db_cache.read_account(a).has_value());
    EXPECT_TRUE(db_cache.read_account(b).has_value());
    EXPECT_TRUE(db_cache.read_account(c).has_value());
    EXPECT_EQ(db_cache.read_account(a).value().balance, uint256_t{10'000});
    EXPECT_EQ(db_cache.read_account(b).value().balance, uint256_t{20'000});
    EXPECT_EQ(db_cache.read_account(c).value().balance, uint256_t{30'000});
    EXPECT_EQ(db_cache.read_storage(b, Incarnation{0, 0}, key1), value1);
    EXPECT_EQ(db_cache.read_storage(b, Incarnation{0, 0}, key2), value2);
    EXPECT_EQ(db_cache.read_storage(c, Incarnation{0, 0}, key1), value1);
    EXPECT_EQ(db_cache.read_storage(c, Incarnation{0, 0}, key2), value2);

    LOG_INFO("block 11 round 111 on block 10 round 100");
    db_cache.set_block_and_prefix(10, bytes32_t{10});
    BlockState bs_111(db_cache, this->vm);
    // b11 r111 r100           +40 v2 --
    {
        State as{bs_111, Incarnation{11, 1}};
        as.add_to_balance(b, 40'000);
        EXPECT_EQ(as.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(as.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_TRUE(bs_111.can_merge(as));
        bs_111.merge(as);
    }
    bs_111.commit(bytes32_t{111}, BlockHeader{.number = 11});
    auto const state_root_round_111 = db_cache.state_root();
    db_cache.set_block_and_prefix(11, bytes32_t{111});
    EXPECT_TRUE(db_cache.read_account(a).has_value());
    EXPECT_TRUE(db_cache.read_account(b).has_value());
    EXPECT_TRUE(db_cache.read_account(c).has_value());
    EXPECT_EQ(db_cache.read_account(a).value().balance, uint256_t{10'000});
    EXPECT_EQ(db_cache.read_account(b).value().balance, uint256_t{60'000});
    EXPECT_EQ(db_cache.read_account(c).value().balance, uint256_t{30'000});
    EXPECT_EQ(db_cache.read_storage(b, Incarnation{0, 0}, key1), value2);
    EXPECT_EQ(db_cache.read_storage(b, Incarnation{0, 0}, key2), bytes32_t{});
    EXPECT_EQ(db_cache.read_storage(c, Incarnation{0, 0}, key1), value1);
    EXPECT_EQ(db_cache.read_storage(c, Incarnation{0, 0}, key2), value2);

    LOG_INFO("block 12 round 121 on block 11 round 111");
    db_cache.set_block_and_prefix(11, bytes32_t{111});
    BlockState bs_121(db_cache, this->vm);
    // b12 r121 r111                        +10    v1
    {
        State as{bs_121, Incarnation{12, 1}};
        as.add_to_balance(c, 10'000);
        EXPECT_EQ(as.set_storage(c, key2, value1), EVMC_STORAGE_MODIFIED);
        EXPECT_TRUE(bs_121.can_merge(as));
        bs_121.merge(as);
    }
    bs_121.commit(bytes32_t{121}, BlockHeader{.number = 12});
    db_cache.set_block_and_prefix(12, bytes32_t{121});
    EXPECT_TRUE(db_cache.read_account(a).has_value());
    EXPECT_TRUE(db_cache.read_account(b).has_value());
    EXPECT_TRUE(db_cache.read_account(c).has_value());
    EXPECT_EQ(db_cache.read_account(a).value().balance, uint256_t{10'000});
    EXPECT_EQ(db_cache.read_account(b).value().balance, uint256_t{60'000});
    EXPECT_EQ(db_cache.read_account(c).value().balance, uint256_t{40'000});
    EXPECT_EQ(db_cache.read_storage(b, Incarnation{0, 0}, key1), value2);
    EXPECT_EQ(db_cache.read_storage(b, Incarnation{0, 0}, key2), bytes32_t{});
    EXPECT_EQ(db_cache.read_storage(c, Incarnation{0, 0}, key1), value1);
    EXPECT_EQ(db_cache.read_storage(c, Incarnation{0, 0}, key2), value1);

    LOG_INFO("block 11 round 112 on block 10 round 100");
    db_cache.set_block_and_prefix(10, bytes32_t{10});
    BlockState bs_112(db_cache, this->vm);
    // b11 r112 r100    +20        --           --
    {
        State as{bs_112, Incarnation{11, 1}};
        as.add_to_balance(a, 20'000);
        EXPECT_EQ(as.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(as.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_TRUE(bs_112.can_merge(as));
        bs_112.merge(as);
    }
    bs_112.commit(bytes32_t{112}, BlockHeader{.number = 11});

    LOG_INFO("block 12 round 122 on block 11 round 112");
    db_cache.set_block_and_prefix(11, bytes32_t{112});
    BlockState bs_122(db_cache, this->vm);
    //  b12 r122 r112           +20 v3              v1
    {
        State as{bs_122, Incarnation{12, 1}};
        as.add_to_balance(b, 20'000);
        EXPECT_EQ(as.set_storage(b, key1, value3), EVMC_STORAGE_ADDED);
        EXPECT_TRUE(bs_122.can_merge(as));
        bs_122.merge(as);
    }
    bs_122.commit(bytes32_t{122}, BlockHeader{.number = 12});

    LOG_INFO("block 13 round 131 on block 12 round 121");
    db_cache.set_block_and_prefix(12, bytes32_t{121});
    BlockState bs_131(db_cache, this->vm);
    //  b13 r131 r121    +30    +20    v1        v2 __
    {
        State as{bs_131, Incarnation{13, 1}};
        as.add_to_balance(a, 30'000);
        as.add_to_balance(b, 20'000);
        EXPECT_EQ(as.set_storage(b, key2, value1), EVMC_STORAGE_ADDED);
        EXPECT_EQ(as.set_storage(c, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(as.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_TRUE(bs_131.can_merge(as));
        bs_131.merge(as);
    }
    bs_131.commit(bytes32_t{131}, BlockHeader{.number = 13});
    auto const state_root_round_131 = db_cache.state_root();

    LOG_INFO("block 13 round 132 on block 12 round 122");
    db_cache.set_block_and_prefix(12, bytes32_t{122});
    BlockState bs_132(db_cache, this->vm);
    // b13 r132 r122                  --        v3
    {
        State as{bs_132, Incarnation{13, 1}};
        EXPECT_EQ(as.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(as.set_storage(c, key1, value3), EVMC_STORAGE_ADDED);
        EXPECT_TRUE(bs_132.can_merge(as));
        bs_132.merge(as);
    }
    bs_132.commit(bytes32_t{132}, BlockHeader{.number = 13});

    //  b10 r100        a 10   b 20 v1 v2   c 30 v1 v2
    //  b11 r111 r100           +40 v2 --
    //  b12 r121 r111                        +10    v1
    //  b13 r131 r121    +30    +20    v1        v2 --
    //                  a 40   b 80 v2 v1   c 40 v2 --
    //  finalize r111 r121 r131
    db_cache.finalize(11, bytes32_t{111});
    db_cache.finalize(12, bytes32_t{121});
    db_cache.finalize(13, bytes32_t{131});

    db_cache.set_block_and_prefix(13, bytes32_t{131});
    EXPECT_TRUE(db_cache.read_account(a).has_value());
    EXPECT_TRUE(db_cache.read_account(b).has_value());
    EXPECT_TRUE(db_cache.read_account(c).has_value());
    EXPECT_EQ(db_cache.read_account(a).value().balance, 40'000);
    EXPECT_EQ(db_cache.read_account(b).value().balance, 80'000);
    EXPECT_EQ(db_cache.read_account(c).value().balance, 40'000);
    EXPECT_EQ(db_cache.read_storage(b, Incarnation{0, 0}, key1), value2);
    EXPECT_EQ(db_cache.read_storage(b, Incarnation{0, 0}, key2), value1);
    EXPECT_EQ(db_cache.read_storage(c, Incarnation{0, 0}, key1), value2);
    EXPECT_EQ(db_cache.read_storage(c, Incarnation{0, 0}, key2), bytes32_t{});

    // check state root of previous rounds
    auto const data_111 = this->db.get_data(
        mpt::concat(proposal_prefix(bytes32_t{111}), STATE_NIBBLE), 11);
    ASSERT_TRUE(data_111.has_value());
    EXPECT_EQ(state_root_round_111, to_bytes(data_111.value()));
    auto const data_131 = this->db.get_data(
        mpt::concat(proposal_prefix(bytes32_t{131}), STATE_NIBBLE), 13);
    ASSERT_TRUE(data_131.has_value());
    EXPECT_EQ(state_root_round_131, to_bytes(data_131.value()));
}

namespace
{
    using Dist = std::uniform_int_distribution<uint64_t>;

    struct RandomProposalGenerator
    {
        static constexpr uint64_t RANDOM_LONG = 10;
        static constexpr uint64_t RANDOM_WIDE = 11;
        static constexpr uint64_t RANDOM_PROPOSE = 12;
        static constexpr uint64_t RANDOM_ADD = 20;
        static constexpr uint64_t RANDOM_DEL = 40;
        static constexpr uint8_t ADDR[] = {81, 82, 83, 84, 85, 86, 87, 88, 89};
        static constexpr uint8_t KEYS[] = {1, 2, 3, 4, 5, 6, 7, 8, 9};

        std::mt19937_64 rng_;
        Db &db1_;
        Db &db2_;
        vm::VM &vm_;
        uint64_t finalized_block_{0};
        uint64_t finalized_proposal_seed_{0};
        uint64_t highest_proposal_seed_{0};
        uint64_t long_{0}; // build a long chain of proposals before finalize
        uint64_t wide_{0}; // different proposals for the same block
        uint64_t wide_parent_{0}; // parent of the wide proposal
        // proposal seed -> {block_number, parent_seed}
        std::map<uint64_t, std::pair<uint64_t, std::optional<uint64_t>>>
            proposals_;
        // block_number -> set of proposals
        std::map<uint64_t, std::set<uint64_t>> blocks_;

        bytes32_t get_dummy_block_id(uint64_t const seed)
        {
            return to_bytes(
                blake3(mpt::serialize_as_big_endian<sizeof(seed)>(seed)));
        }

    public:
        RandomProposalGenerator(
            uint64_t const seed, Db &db1, Db &db2, vm::VM &vm)
            : rng_(seed)
            , db1_(db1)
            , db2_(db2)
            , vm_(vm)
        {
        }

        void run(uint64_t iterations)
        {
            for (uint64_t i = 0; i < iterations; ++i) {
                LOG_INFO("=== Iteration {}", i + 1);
                std::optional<uint64_t> parent = {};
                uint64_t proposal_seed = 0;
                uint64_t block = 0;
                // long
                if (long_) {
                    LOG_INFO("_long_ {}", long_);
                    parent = last_proposal_seed();
                    proposal_seed = last_proposal_seed() + 1;
                    block = last_proposal_block() + 1;
                    --long_;
                }
                // wide
                else if (wide_) {
                    LOG_INFO("_wide_ {}", wide_, wide_parent_);
                    parent = wide_parent_;
                    MONAD_ASSERT(proposals_.find(*parent) != proposals_.end());
                    proposal_seed = highest_proposal_seed_ + 1;
                    block = proposals_[*parent].first + 1;
                    --wide_;
                }
                // empty
                else if (blocks_.empty()) {
                    LOG_INFO("_empty_");
                    proposal_seed = highest_proposal_seed_ + 1;
                    block = finalized_block_ + 1;
                    parent = finalized_block_ == 0
                                 ? std::nullopt
                                 : std::make_optional(finalized_proposal_seed_);
                }
                // random propose
                else if (random_propose()) {
                    LOG_INFO("_random_propose_");
                    proposal_seed = highest_proposal_seed_ + 1;
                    Dist dist(0, proposals_.size());
                    uint64_t const order = dist(rng_);
                    if (order == 0) {
                        block = finalized_block_ + 1;
                    }
                    else {
                        auto it = proposals_.begin();
                        MONAD_ASSERT(it != proposals_.end());
                        for (uint64_t i = 1; i < order; ++i) {
                            ++it;
                            MONAD_ASSERT(it != proposals_.end());
                        }
                        block = it->second.first + 1;
                        parent = it->first;
                        MONAD_ASSERT(parent);
                    }
                }
                // propose
                if (proposal_seed) {
                    LOG_INFO("Propose_ {} {} {}", block, proposal_seed, parent);
                    MONAD_ASSERT(block);
                    auto const it = proposals_.find(proposal_seed);
                    MONAD_ASSERT(it == proposals_.end()); // assert no duplicate
                    proposals_[proposal_seed] = {block, parent};
                    blocks_[block].insert(proposal_seed);
                    propose(block, proposal_seed, parent);
                    highest_proposal_seed_ =
                        proposal_seed > highest_proposal_seed_
                            ? proposal_seed
                            : highest_proposal_seed_;
                    // future random
                    if (long_ == 0 && wide_ == 0) {
                        if (random_long()) {
                            long_ = random9();
                        }
                        else if (random_wide()) {
                            wide_ = random9();
                            wide_parent_ = proposal_seed;
                        }
                    }
                }
                // finalize
                else {
                    finalize();
                }
                // check
                check();
            }
        }

    private:
        uint64_t last_proposal_seed() const
        {
            return proposals_.empty() ? highest_proposal_seed_
                                      : proposals_.rbegin()->first;
        }

        uint64_t last_proposal_block() const
        {
            return proposals_.empty() ? finalized_block_
                                      : proposals_.rbegin()->second.first;
        }

        bool random_long()
        {
            return random100() < RANDOM_LONG;
        }

        bool random_wide()
        {
            return random100() < RANDOM_WIDE;
        }

        bool random_propose()
        {
            return random100() < RANDOM_PROPOSE;
        }

        uint64_t random100()
        {
            Dist dist(0, 99);
            return dist(rng_);
        }

        uint64_t random9()
        {
            Dist dist(1, 9);
            return dist(rng_);
        }

        uint64_t random_addr()
        {
            return 80 + random9();
        }

        uint64_t random_key()
        {
            return random9();
        }

        void propose(
            uint64_t const block, uint64_t const proposal_seed,
            std::optional<uint64_t> const parent)
        {
            MONAD_ASSERT(block > 0);
            db1_.set_block_and_prefix(
                block - 1,
                parent.has_value() ? get_dummy_block_id(*parent) : bytes32_t{});
            db2_.set_block_and_prefix(
                block - 1,
                parent.has_value() ? get_dummy_block_id(*parent) : bytes32_t{});
            BlockState bs1(db1_, vm_);
            BlockState bs2(db2_, vm_);
            Incarnation inc{block, 1};
            State st1(bs1, inc);
            State st2(bs2, inc);
            uint64_t const num = random9();
            for (uint64_t i = 0; i < num; ++i) {
                Address addr(random_addr());
                uint64_t const action = random100();
                if (action < RANDOM_ADD) {
                    uint256_t const delta = 10 * random9();
                    LOG_INFO(
                        "Account_add_ a_{} {}", addr.bytes[19] % 10, delta);
                    st1.add_to_balance(addr, delta);
                    st2.add_to_balance(addr, delta);
                }
                else if (action < RANDOM_DEL) {
                    auto const account1 = st1.recent_account(addr);
                    auto const account2 = st2.recent_account(addr);
                    MONAD_ASSERT(account1 == account2);
                    if (account1.has_value()) {
                        uint256_t const bal = account1->balance;
                        MONAD_ASSERT(account2->balance == bal);
                        LOG_INFO(
                            "Account_del_ a_{} {}", addr.bytes[19] % 10, bal);
                        st1.subtract_from_balance(addr, bal);
                        st2.subtract_from_balance(addr, bal);
                    }
                    else {
                        LOG_INFO(
                            "Account_del_empty_ a_{}", addr.bytes[19] % 10);
                    }
                }
                else { // SET_STORAGE
                    bytes32_t const key(random_key());
                    LOG_INFO("Account_add_ a_{} {}", addr.bytes[19] % 10, 10);
                    st1.add_to_balance(addr, 10);
                    st2.add_to_balance(addr, 10);
                    bytes32_t val;
                    val.bytes[31] = static_cast<uint8_t>(10 * random9());
                    LOG_INFO(
                        "Set_storage_ a_{} k_{} {}",
                        addr.bytes[19] % 10,
                        key.bytes[31],
                        val.bytes[31]);
                    st1.set_storage(addr, key, val);
                    st2.set_storage(addr, key, val);
                }
            }
            st1.destruct_touched_dead();
            st2.destruct_touched_dead();
            MONAD_ASSERT(bs1.can_merge(st1));
            MONAD_ASSERT(bs2.can_merge(st2));
            bs1.merge(st1);
            bs2.merge(st2);
            bs1.commit(
                get_dummy_block_id(proposal_seed),
                BlockHeader{.number = block});
            bs2.commit(
                get_dummy_block_id(proposal_seed),
                BlockHeader{.number = block});
        }

        void finalize()
        {
            // block
            MONAD_ASSERT(!blocks_.empty());
            auto const it = blocks_.begin();
            uint64_t block = it->first;
            // proposal
            auto &s1 = it->second; // set of proposals
            for (auto it2 = s1.begin(); it2 != s1.end();) {
                auto const it3 = proposals_.find(*it2);
                MONAD_ASSERT(it3 != proposals_.end());
                MONAD_ASSERT(it3->second.first == block);
                auto const p = it3->second.second;
                if (p.has_value() && *p != finalized_proposal_seed_) {
                    it2 = s1.erase(it2);
                }
                else {
                    ++it2;
                }
            }
            if (s1.empty()) {
                LOG_INFO("No_valid_proposals_to_finalize_");
                proposals_.clear();
                blocks_.clear();
                return;
            }
            uint64_t const target = s1.size() * random100() / 100;
            MONAD_ASSERT(target < s1.size());
            auto it2 = s1.begin();
            for (uint64_t i = 0; i < target; ++i) {
                ++it2;
            }
            MONAD_ASSERT(it2 != s1.end());
            uint64_t const proposal_seed = *it2;
            MONAD_ASSERT(proposals_.find(proposal_seed) != proposals_.end());
            MONAD_ASSERT(proposals_[proposal_seed].first == block);
            LOG_INFO("Finalize_ {} {}", block, proposal_seed);
            // db finalize
            db1_.finalize(block, get_dummy_block_id(proposal_seed));
            db2_.finalize(block, get_dummy_block_id(proposal_seed));
            finalized_block_ = block;
            finalized_proposal_seed_ = proposal_seed;
            // remove block and proposals
            for (auto const r : s1) {
                auto it3 = proposals_.find(r);
                MONAD_ASSERT(it3 != proposals_.end());
                proposals_.erase(it3);
            }
            blocks_.erase(it);
            while (!proposals_.empty()) {
                auto const it3 = proposals_.begin();
                MONAD_ASSERT(it3->first != proposal_seed);
                if (it3->first > proposal_seed) {
                    break;
                }
                if (it3->second.first > block) {
                    MONAD_ASSERT(
                        blocks_.find(it3->second.first) != blocks_.end());
                    auto &s2 = blocks_[it3->second.first];
                    auto it4 = s2.find(it3->first);
                    MONAD_ASSERT(it4 != s2.end());
                    s2.erase(it4);
                }
                proposals_.erase(it3);
            }
        }

        void check()
        {
            for (uint8_t const i : ADDR) {
                Address addr(i);
                auto account1 = db1_.read_account(addr);
                auto account2 = db2_.read_account(addr);
                if (account1) {
                    LOG_INFO(
                        "Check_account_ a_{} {:08} {}",
                        addr.bytes[19] % 10,
                        account1->incarnation.get_block(),
                        account1->balance);
                }
                MONAD_ASSERT(account1 == account2);
                if (account1) {
                    Incarnation incarnation = account1->incarnation;
                    for (uint8_t const j : KEYS) {
                        bytes32_t key(j);
                        auto const val1 =
                            db1_.read_storage(addr, incarnation, key);
                        auto const val2 =
                            db2_.read_storage(addr, incarnation, key);
                        if (val1 != bytes32_t{0}) {
                            LOG_INFO(
                                "Check_storage_ a_{}          k_{} {}",
                                addr.bytes[19] % 10,
                                key.bytes[31],
                                val1.bytes[31]);
                        }
                        if (val1 != val2) {
                            LOG_INFO(
                                "Check_storage_ a_{}          k_{} {}",
                                addr.bytes[19] % 10,
                                key.bytes[31],
                                val2.bytes[31]);
                        }
                        MONAD_ASSERT(val1 == val2);
                    }
                }
            }
        }
    };
}

TEST_F(TwoOnDisk, random_proposals)
{
    load_header(this->db1, BlockHeader{.number = 0});
    load_header(this->db2, BlockHeader{.number = 0});
    TrieDb &db1 = this->tdb1;
    DbCache db2(this->tdb2);

    uint64_t const seed = [] {
        char const *str = std::getenv("MONAD_RANDOM_PROPOSALS_SEED");
        return str ? std::stoull(std::string(str)) : 0;
    }();
    std::unique_ptr<RandomProposalGenerator> gen(
        new RandomProposalGenerator(seed, db1, db2, this->vm));
    uint64_t const iters = [] {
        char const *str = std::getenv("MONAD_RANDOM_PROPOSALS_ITERATIONS");
        return str ? std::stoull(std::string(str)) : 100;
    }();
    LOG_INFO(
        "Random proposal generation: {} iterations with seed {}", iters, seed);
    gen->run(iters);
}
