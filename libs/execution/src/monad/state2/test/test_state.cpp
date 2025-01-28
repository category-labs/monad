#include <monad/core/account.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/db_cache.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/code_analysis.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <memory>
#include <optional>

using namespace monad;

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
    auto const code_analysis1 = std::make_shared<CodeAnalysis>(analyze(code1));
    constexpr auto code2 =
        byte_string{0x6e, 0x65, 0x20, 0x2d, 0x20, 0x45, 0x55, 0x31, 0x34};
    auto const code_analysis2 = std::make_shared<CodeAnalysis>(analyze(code2));

    struct InMemoryTrieDbFixture : public ::testing::Test
    {
        InMemoryMachine machine;
        mpt::Db db{machine};
        TrieDb tdb{db};
    };

    struct OnDiskTrieDbFixture : public ::testing::Test
    {
        OnDiskMachine machine;
        mpt::Db db{machine, mpt::OnDiskDbConfig{}};
        TrieDb tdb{db};
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 10'000}}}}},
        Code{},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};

    EXPECT_TRUE(s.account_exists(a));
    EXPECT_FALSE(s.account_exists(b));
}

TYPED_TEST(StateTest, create_contract)
{
    BlockState bs{this->tdb};

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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};

    State s{bs, Incarnation{1, 1}};
    s.set_nonce(b, 1);

    EXPECT_EQ(s.get_nonce(b), 1);
}

TYPED_TEST(StateTest, get_code_hash)
{
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};

    State s{bs, Incarnation{1, 1}};
    s.create_contract(b);
    s.set_code_hash(b, hash1);

    EXPECT_EQ(s.get_code_hash(b), hash1);
}

TYPED_TEST(StateTest, selfdestruct)
{
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
        bs.commit({}, {}, {}, {}, {}, {}, std::nullopt);
        EXPECT_EQ(
            this->tdb.read_storage(a, Incarnation{1, 2}, key1), bytes32_t{});
    }
}

TYPED_TEST(StateTest, selfdestruct_merge_create_commit_incarnation)
{
    BlockState bs{this->tdb};
    this->tdb.commit(
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
        bs.commit({}, {}, {}, {}, {}, {}, std::nullopt);
        EXPECT_EQ(this->tdb.read_storage(a, Incarnation{1, 2}, key1), value1);
        EXPECT_EQ(this->tdb.read_storage(a, Incarnation{1, 2}, key2), value2);
        EXPECT_EQ(
            this->tdb.state_root(),
            0x5B853ED6066181BF0E0D405DA0926FD7707446BCBE670DE13C9EDA7A84F6A401_bytes32);
    }
}

TYPED_TEST(StateTest, selfdestruct_create_destroy_create_commit_incarnation)
{
    BlockState bs{this->tdb};
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
        bs.commit({}, {}, {}, {}, {}, {}, std::nullopt);
        EXPECT_EQ(
            this->tdb.read_storage(a, Incarnation{1, 2}, key1), bytes32_t{});
        EXPECT_EQ(this->tdb.read_storage(a, Incarnation{1, 2}, key2), value3);
    }
}

TYPED_TEST(StateTest, create_conflict_address_incarnation)
{
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};

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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};

    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    this->tdb.commit(
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
    BlockState bs{this->tdb};
    Account acct{.code_hash = code_hash1};
    this->tdb.commit(
        StateDeltas{{a, StateDelta{.account = {std::nullopt, acct}}}},
        Code{{code_hash1, code_analysis1}},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};
    EXPECT_EQ(s.get_code_size(a), code1.size());
}

TYPED_TEST(StateTest, copy_code)
{
    BlockState bs{this->tdb};
    Account acct_a{.code_hash = code_hash1};
    Account acct_b{.code_hash = code_hash2};

    this->tdb.commit(
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, acct_a}}},
            {b, StateDelta{.account = {std::nullopt, acct_b}}}},
        Code{{code_hash1, code_analysis1}, {code_hash2, code_analysis2}},
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

    BlockState bs{this->tdb};

    this->tdb.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.code_hash = code_hash1}}}}},
        Code{{code_hash1, std::make_shared<CodeAnalysis>(analyze(contract))}},
        BlockHeader{});

    State s{bs, Incarnation{1, 1}};

    {
        s.access_account(a);
        auto const c = s.get_code(a);
        EXPECT_EQ(c->executable_code, contract);
    }
    { // non-existant account
        auto const c = s.get_code(b);
        EXPECT_EQ(c->executable_code, byte_string{});
    }
}

TYPED_TEST(StateTest, set_code)
{
    BlockState bs{this->tdb};

    State s{bs, Incarnation{1, 1}};
    s.create_contract(a);
    s.create_contract(b);
    s.set_code(a, code2);
    s.set_code(b, byte_string{});

    EXPECT_EQ(s.get_code(a)->executable_code, code2);
    EXPECT_EQ(s.get_code(b)->executable_code, byte_string{});
}

TYPED_TEST(StateTest, can_merge_same_account_different_storage)
{
    BlockState bs{this->tdb};

    this->tdb.commit(
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
    BlockState bs{this->tdb};

    this->tdb.commit(
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
    BlockState bs{this->tdb};

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
    BlockState bs{this->tdb};
    State as{bs, Incarnation{1, 1}};

    as.create_contract(a);
    as.add_to_balance(a, 1);
    as.set_storage(a, key1, value1);

    bs.merge(as);
    bs.commit({}, {}, {}, {}, {}, {}, std::nullopt);

    EXPECT_TRUE(this->tdb.read_account(a).has_value());
    EXPECT_EQ(this->tdb.read_account(a).value().balance, 1u);
    EXPECT_EQ(this->tdb.read_storage(a, Incarnation{1, 1}, key1), value1);
}

TYPED_TEST(StateTest, set_and_then_clear_storage_in_same_commit)
{
    using namespace intx;
    BlockState bs{this->tdb};
    State as{bs, Incarnation{1, 1}};

    as.create_contract(a);
    EXPECT_EQ(as.set_storage(a, key1, value1), EVMC_STORAGE_ADDED);
    EXPECT_EQ(as.set_storage(a, key1, null), EVMC_STORAGE_ADDED_DELETED);
    bs.merge(as);
    bs.commit({}, {}, {}, {}, {}, {}, std::nullopt);

    EXPECT_EQ(
        this->tdb.read_storage(a, Incarnation{1, 1}, key1), monad::bytes32_t{});
}

TYPED_TEST(StateTest, commit_twice)
{
    load_header(this->db, BlockHeader{.number = 8});

    // commit to Block 9 Finalized
    this->tdb.set_block_and_round(8);
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
        BlockHeader{.number = 9});

    { // Commit to Block 10 Round 5, on top of block 9 finalized
        this->tdb.set_block_and_round(9);
        BlockState bs{this->tdb};
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
        bs.commit({.number = 10}, {}, {}, {}, {}, {}, std::nullopt, 5);
        this->tdb.finalize(10, 5);

        EXPECT_EQ(this->tdb.read_storage(b, Incarnation{1, 1}, key1), value2);
        EXPECT_EQ(this->tdb.read_storage(b, Incarnation{1, 1}, key2), value2);
    }
    { // Commit to Block 11 Round 6, on top of block 10 round 5
        this->tdb.set_block_and_round(10, 5);
        BlockState bs{this->tdb};
        State cs{bs, Incarnation{2, 1}};
        EXPECT_TRUE(cs.account_exists(a));
        EXPECT_TRUE(cs.account_exists(c));
        EXPECT_EQ(cs.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(cs.set_storage(c, key2, value1), EVMC_STORAGE_MODIFIED);
        EXPECT_TRUE(cs.selfdestruct<EVMC_SHANGHAI>(c, a));
        cs.destruct_suicides<EVMC_SHANGHAI>();
        EXPECT_TRUE(bs.can_merge(cs));
        bs.merge(cs);
        bs.commit({.number = 11}, {}, {}, {}, {}, {}, std::nullopt, 6);
    }
    EXPECT_EQ(
        this->tdb.read_storage(c, Incarnation{2, 1}, key1), monad::bytes32_t{});
    EXPECT_EQ(
        this->tdb.read_storage(c, Incarnation{2, 1}, key2), monad::bytes32_t{});

    // verify finalized state is the same as round 6
    this->tdb.finalize(11, 6);
    this->tdb.set_block_and_round(11);
    EXPECT_EQ(
        this->tdb.read_storage(c, Incarnation{2, 1}, key1), monad::bytes32_t{});
    EXPECT_EQ(
        this->tdb.read_storage(c, Incarnation{2, 1}, key2), monad::bytes32_t{});
}

TEST_F(OnDiskTrieDbFixture, commit_multiple_proposals)
{
    // This test would fail with DbCache
    load_header(this->db, BlockHeader{.number = 9});

    // commit to block 10, round 5
    this->tdb.set_block_and_round(9);
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
        BlockHeader{.number = 10},
        {},
        {},
        {},
        {},
        {},
        std::nullopt,
        5);
    {
        // set to block 10 round 5
        this->tdb.set_block_and_round(10, 5);
        BlockState bs{this->tdb};
        State as{bs, Incarnation{1, 1}};
        EXPECT_TRUE(as.account_exists(b));
        as.add_to_balance(b, 42'000);
        as.set_nonce(b, 3);
        EXPECT_EQ(as.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(as.set_storage(b, key2, null), EVMC_STORAGE_DELETED);

        EXPECT_TRUE(bs.can_merge(as));
        bs.merge(as);
        // Commit block 11 round 8 on top of block 10 round 5
        bs.commit({.number = 11}, {}, {}, {}, {}, {}, std::nullopt, 8);

        EXPECT_EQ(this->tdb.read_account(b).value().balance, 82'000);
        EXPECT_EQ(this->tdb.read_storage(b, Incarnation{1, 1}, key1), value2);
        EXPECT_EQ(
            this->tdb.read_storage(b, Incarnation{1, 1}, key2), bytes32_t{});
    }
    auto const state_root_round8 = this->tdb.state_root();

    {
        // set to block 10 round 5
        this->tdb.set_block_and_round(10, 5);
        BlockState bs{this->tdb};
        State as{bs, Incarnation{1, 1}};
        EXPECT_TRUE(as.account_exists(b));
        as.add_to_balance(b, 44'000);
        as.set_nonce(b, 3);
        EXPECT_EQ(as.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(as.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_TRUE(bs.can_merge(as));
        bs.merge(as);
        // Commit block 11 round 6 on top of block 10 round 5
        bs.commit({.number = 11}, {}, {}, {}, {}, {}, std::nullopt, 6);

        EXPECT_EQ(this->tdb.read_account(b).value().balance, 84'000);
        EXPECT_EQ(
            this->tdb.read_storage(b, Incarnation{1, 1}, key1), bytes32_t{});
        EXPECT_EQ(
            this->tdb.read_storage(b, Incarnation{1, 1}, key2), bytes32_t{});
    }

    auto const state_root_round6 = this->tdb.state_root();

    {
        // set to block 10 round 5
        this->tdb.set_block_and_round(10, 5);
        BlockState bs{this->tdb};
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
        bs.commit({.number = 11}, {}, {}, {}, {}, {}, std::nullopt, 7);

        EXPECT_EQ(this->tdb.read_account(b).value().balance, 72'000);
        EXPECT_EQ(this->tdb.read_storage(b, Incarnation{1, 1}, key1), value2);
        EXPECT_EQ(this->tdb.read_storage(b, Incarnation{1, 1}, key2), value3);
    }
    auto const state_root_round7 = this->tdb.state_root();
    this->tdb.finalize(11, 7);
    this->tdb.set_block_and_round(11); // set to block 11 finalized
    EXPECT_EQ(state_root_round7, this->tdb.state_root());

    // check state root of previous rounds
    this->tdb.set_block_and_round(11, 6);
    EXPECT_EQ(state_root_round6, this->tdb.state_root());

    this->tdb.set_block_and_round(11, 8);
    EXPECT_EQ(state_root_round8, this->tdb.state_root());
}

#if MMM_DIFF
TEST_F(OnDiskTrieDbFixture, proposal_basics)
{
    load_header(this->db, BlockHeader{.number = 9});
    Db &db = this->tdb;
    db.set_block_and_round(9);
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 30'000}}}}},
        Code{},
        BlockHeader{.number = 10},
        {},
        {},
        {},
        {},
        {},
        std::nullopt,
        100);
    db.set_block_and_round(10, 100);
    EXPECT_EQ(db.read_account(a).value().balance, 30'000);

    DbCache db_cache(db);
    db_cache.set_block_and_round(10, 100);
    BlockState bs1(db_cache);
    EXPECT_EQ(bs1.read_account(a).value().balance, 30'000);
    bs1.commit(BlockHeader{.number = 11}, {}, {}, {}, {}, {}, {}, 101);
    db_cache.finalize(11, 101);

    db_cache.set_block_and_round(11, 101);
    BlockState bs2(db_cache);
    State as{bs2, Incarnation{1, 1}};
    EXPECT_TRUE(as.account_exists(a));
    as.add_to_balance(a, 10'000);
    EXPECT_TRUE(bs2.can_merge(as));
    bs2.merge(as);
    EXPECT_EQ(db_cache.read_account(a).value().balance, 30'000);
    bs2.commit({.number = 12}, {}, {}, {}, {}, {}, std::nullopt, 102);
    EXPECT_EQ(db_cache.read_account(a).value().balance, 40'000);
    db_cache.finalize(12, 102);
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
    std::unique_ptr<Code> code{new Code{}};
    db_cache.set_block_and_round(9);
    db_cache.commit(
        state_deltas,
        code,
        BlockHeader{.number = 10},
        {},
        {},
        {},
        {},
        {},
        {},
        100);
    db_cache.finalize(10, 100);
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
    db_cache.set_block_and_round(10, 100);
    BlockState bs_111(db_cache);
    // b11 r111 r100           +40 v2 --
    {
        State as{bs_111, Incarnation{11, 1}};
        as.add_to_balance(b, 40'000);
        EXPECT_EQ(as.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(as.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_TRUE(bs_111.can_merge(as));
        bs_111.merge(as);
    }
    bs_111.commit({.number = 11}, {}, {}, {}, {}, {}, std::nullopt, 111);
    auto const state_root_round_111 = db_cache.state_root();
    db_cache.set_block_and_round(11, 111);
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
    db_cache.set_block_and_round(11, 111);
    BlockState bs_121(db_cache);
    // b12 r121 r111                        +10    v1
    {
        State as{bs_121, Incarnation{12, 1}};
        as.add_to_balance(c, 10'000);
        EXPECT_EQ(as.set_storage(c, key2, value1), EVMC_STORAGE_MODIFIED);
        EXPECT_TRUE(bs_121.can_merge(as));
        bs_121.merge(as);
    }
    bs_121.commit({.number = 12}, {}, {}, {}, {}, {}, std::nullopt, 121);
    db_cache.set_block_and_round(12, 121);
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
    db_cache.set_block_and_round(10, 100);
    BlockState bs_112(db_cache);
    // b11 r112 r100    +20        --           --
    {
        State as{bs_112, Incarnation{11, 1}};
        as.add_to_balance(a, 20'000);
        EXPECT_EQ(as.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(as.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_TRUE(bs_112.can_merge(as));
        bs_112.merge(as);
    }
    bs_112.commit({.number = 11}, {}, {}, {}, {}, {}, std::nullopt, 112);

    LOG_INFO("block 12 round 122 on block 11 round 112");
    db_cache.set_block_and_round(11, 112);
    BlockState bs_122(db_cache);
    //  b12 r122 r112           +20 v3              v1
    {
        State as{bs_122, Incarnation{12, 1}};
        as.add_to_balance(b, 20'000);
        EXPECT_EQ(as.set_storage(b, key1, value3), EVMC_STORAGE_ADDED);
        EXPECT_TRUE(bs_122.can_merge(as));
        bs_122.merge(as);
    }
    bs_122.commit({.number = 12}, {}, {}, {}, {}, {}, std::nullopt, 122);

    LOG_INFO("block 13 round 131 on block 12 round 121");
    db_cache.set_block_and_round(12, 121);
    BlockState bs_131(db_cache);
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
    bs_131.commit({.number = 13}, {}, {}, {}, {}, {}, std::nullopt, 131);
    auto const state_root_round_131 = db_cache.state_root();

    LOG_INFO("block 13 round 132 on block 12 round 122");
    db_cache.set_block_and_round(12, 122);
    BlockState bs_132(db_cache);
    // b13 r132 r122                  --        v3
    {
        State as{bs_132, Incarnation{13, 1}};
        EXPECT_EQ(as.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(as.set_storage(c, key1, value3), EVMC_STORAGE_ADDED);
        EXPECT_TRUE(bs_132.can_merge(as));
        bs_132.merge(as);
    }
    bs_132.commit({.number = 13}, {}, {}, {}, {}, {}, std::nullopt, 132);

    //  b10 r100        a 10   b 20 v1 v2   c 30 v1 v2
    //  b11 r111 r100           +40 v2 --
    //  b12 r121 r111                        +10    v1
    //  b13 r131 r121    +30    +20    v1        v2 --
    //                  a 40   b 80 v2 v1   c 40 v2 --
    //  finalize r111 r121 r131
    db_cache.finalize(11, 111);
    db_cache.finalize(12, 121);
    db_cache.finalize(13, 131);

    db_cache.set_block_and_round(13, 131);
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
        mpt::concat(
            PROPOSAL_NIBBLE,
            mpt::NibblesView{
                mpt::serialize_as_big_endian<sizeof(uint64_t)>(111ull)},
            STATE_NIBBLE),
        11);
    ASSERT_TRUE(data_111.has_value());
    EXPECT_EQ(state_root_round_111, to_bytes(data_111.value()));
    auto const data_131 = this->db.get_data(
        mpt::concat(
            PROPOSAL_NIBBLE,
            mpt::NibblesView{
                mpt::serialize_as_big_endian<sizeof(uint64_t)>(131ull)},
            STATE_NIBBLE),
        13);
    ASSERT_TRUE(data_131.has_value());
    EXPECT_EQ(state_root_round_131, to_bytes(data_131.value()));
}
#endif
