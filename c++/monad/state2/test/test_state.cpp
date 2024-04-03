#include <monad/core/account.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/trie_db.hpp>
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
        TrieDb db{std::nullopt};
    };

    struct OnDiskTrieDbFixture : public ::testing::Test
    {
        TrieDb db{mpt::OnDiskDbConfig{}};
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
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 10'000}}}}},
        Code{});

    State s{bs};

    EXPECT_EQ(s.access_account(a), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_account(a), EVMC_ACCESS_WARM);
    EXPECT_EQ(s.access_account(b), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_account(b), EVMC_ACCESS_WARM);
}

TYPED_TEST(StateTest, account_exists)
{
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 10'000}}}}},
        Code{});

    State s{bs};

    EXPECT_TRUE(s.account_exists(a));
    EXPECT_FALSE(s.account_exists(b));
}

TYPED_TEST(StateTest, create_contract)
{
    BlockState bs{this->db};

    State s{bs};
    s.create_contract(a);
    EXPECT_TRUE(s.account_exists(a));

    // allow pre-existing empty account
    EXPECT_FALSE(s.account_exists(b));
    s.create_contract(b);
    EXPECT_TRUE(s.account_exists(b));
}

TYPED_TEST(StateTest, get_balance)
{
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 10'000}}}}},
        Code{});

    State s{bs};

    EXPECT_EQ(s.get_balance(a), bytes32_t{10'000});
    EXPECT_EQ(s.get_balance(b), bytes32_t{0});
    EXPECT_EQ(s.get_balance(c), bytes32_t{0});
}

TYPED_TEST(StateTest, add_to_balance)
{
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, Account{.balance = 1}}}}},
        Code{});

    State s{bs};
    s.add_to_balance(a, 10'000);
    s.add_to_balance(b, 20'000);

    EXPECT_EQ(s.get_balance(a), bytes32_t{10'001});
    EXPECT_EQ(s.get_balance(b), bytes32_t{20'000});
}

TYPED_TEST(StateTest, get_nonce)
{
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, Account{.nonce = 2}}}}},
        Code{});

    State s{bs};

    EXPECT_EQ(s.get_nonce(a), 2);
    EXPECT_EQ(s.get_nonce(b), 0);
    EXPECT_EQ(s.get_nonce(c), 0);
}

TYPED_TEST(StateTest, set_nonce)
{
    BlockState bs{this->db};

    State s{bs};
    s.set_nonce(b, 1);

    EXPECT_EQ(s.get_nonce(b), 1);
}

TYPED_TEST(StateTest, get_code_hash)
{
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.code_hash = hash1}}}}},
        Code{});

    State s{bs};

    EXPECT_EQ(s.get_code_hash(a), hash1);
    EXPECT_EQ(s.get_code_hash(b), NULL_HASH);
    EXPECT_EQ(s.get_code_hash(c), NULL_HASH);
}

TYPED_TEST(StateTest, set_code_hash)
{
    BlockState bs{this->db};

    State s{bs};
    s.create_contract(b);
    s.set_code_hash(b, hash1);

    EXPECT_EQ(s.get_code_hash(b), hash1);
}

TYPED_TEST(StateTest, selfdestruct)
{
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {a,
             StateDelta{.account = {std::nullopt, Account{.balance = 18'000}}}},
            {c,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 38'000}}}}},
        Code{});

    State s{bs};
    s.create_contract(b);
    s.add_to_balance(b, 28'000);

    EXPECT_TRUE(s.selfdestruct(a, c));
    EXPECT_EQ(s.get_balance(a), bytes32_t{});
    EXPECT_EQ(s.get_balance(c), bytes32_t{56'000});
    EXPECT_FALSE(s.selfdestruct(a, c));

    EXPECT_TRUE(s.selfdestruct(b, c));
    EXPECT_EQ(s.get_balance(b), bytes32_t{});
    EXPECT_EQ(s.get_balance(c), bytes32_t{84'000});
    EXPECT_FALSE(s.selfdestruct(b, c));

    s.destruct_suicides();
    EXPECT_FALSE(s.account_exists(a));
    EXPECT_FALSE(s.account_exists(b));
}

TYPED_TEST(StateTest, selfdestruct_self)
{
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 18'000}}}}},
        Code{});

    State s{bs};

    EXPECT_TRUE(s.selfdestruct(a, a));
    EXPECT_EQ(s.get_balance(a), bytes32_t{});

    s.destruct_suicides();
    EXPECT_FALSE(s.account_exists(a));
}

TYPED_TEST(StateTest, selfdestruct_merge_incarnation)
{
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 18'000}},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{});
    {
        State s1{bs};

        s1.selfdestruct(a, a);
        s1.destruct_suicides();

        EXPECT_TRUE(bs.can_merge(s1));
        bs.merge(s1);
    }
    {
        State s2{bs};
        EXPECT_FALSE(s2.account_exists(a));
        s2.create_contract(a);
        EXPECT_EQ(s2.get_storage(a, key1), bytes32_t{});
    }
}

TYPED_TEST(StateTest, selfdestruct_merge_create_incarnation)
{
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 18'000}},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{});
    {
        State s1{bs};

        s1.selfdestruct(a, b);
        s1.destruct_suicides();

        EXPECT_TRUE(bs.can_merge(s1));
        bs.merge(s1);
    }
    {
        State s2{bs};
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
        State s3{bs};
        EXPECT_TRUE(s3.account_exists(a));
        EXPECT_EQ(s3.get_storage(a, key1), value2);
        EXPECT_EQ(s3.get_storage(a, key2), value1);
    }
}

TYPED_TEST(StateTest, selfdestruct_merge_commit_incarnation)
{
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 18'000}},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{});
    {
        State s1{bs};

        s1.selfdestruct(a, a);
        s1.destruct_suicides();

        EXPECT_TRUE(bs.can_merge(s1));
        bs.merge(s1);
    }
    {
        State s2{bs};
        s2.create_contract(a);
        bs.merge(s2);
    }
    {
        bs.commit();
        EXPECT_EQ(this->db.read_storage(a, key1), bytes32_t{});
    }
}

TYPED_TEST(StateTest, selfdestruct_merge_create_commit_incarnation)
{
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage =
                     {{key1, {bytes32_t{}, value2}},
                      {key3, {bytes32_t{}, value3}}}}}},
        Code{});
    {
        State s1{bs};

        s1.selfdestruct(a, a);
        s1.destruct_suicides();

        EXPECT_TRUE(bs.can_merge(s1));
        bs.merge(s1);
    }
    {
        State s2{bs};
        s2.add_to_balance(a, 1000);

        s2.set_storage(a, key1, value1);
        s2.set_storage(a, key2, value2);

        EXPECT_TRUE(bs.can_merge(s2));
        bs.merge(s2);
    }
    {
        bs.commit();
        EXPECT_EQ(this->db.read_storage(a, key1), value1);
        EXPECT_EQ(this->db.read_storage(a, key2), value2);
        EXPECT_EQ(
            this->db.state_root(),
            0x5B853ED6066181BF0E0D405DA0926FD7707446BCBE670DE13C9EDA7A84F6A401_bytes32);
    }
}

TYPED_TEST(StateTest, selfdestruct_create_destroy_create_commit_incarnation)
{
    BlockState bs{this->db};
    {
        State s1{bs};

        s1.create_contract(a);
        s1.set_storage(a, key1, value1);
        s1.selfdestruct(a, b);
        s1.destruct_suicides();

        EXPECT_TRUE(bs.can_merge(s1));
        bs.merge(s1);
    }
    {
        State s2{bs};
        s2.create_contract(a);

        s2.set_storage(a, key2, value3);

        EXPECT_TRUE(bs.can_merge(s2));
        bs.merge(s2);
    }
    {
        bs.commit();
        EXPECT_EQ(this->db.read_storage(a, key1), bytes32_t{});
        EXPECT_EQ(this->db.read_storage(a, key2), value3);
    }
}

TYPED_TEST(StateTest, create_conflict_address_incarnation)
{
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 18'000}},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{});

    State s1{bs};

    s1.create_contract(a);
    s1.set_storage(a, key2, value2);

    EXPECT_EQ(s1.get_storage(a, key1), bytes32_t{});
    EXPECT_EQ(s1.get_storage(a, key2), value2);
}

TYPED_TEST(StateTest, destruct_touched_dead)
{
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {a,
             StateDelta{.account = {std::nullopt, Account{.balance = 10'000}}}},
            {b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});

    State s{bs};
    EXPECT_TRUE(s.account_exists(a));
    s.destruct_touched_dead();
    s.destruct_suicides();
    EXPECT_TRUE(s.account_exists(a));
    EXPECT_TRUE(s.account_exists(b));

    s.subtract_from_balance(a, 10'000);
    s.destruct_touched_dead();
    s.destruct_suicides();

    EXPECT_FALSE(s.account_exists(a));
    EXPECT_TRUE(s.account_exists(b));

    s.touch(b);
    s.destruct_touched_dead();
    s.destruct_suicides();
    EXPECT_FALSE(s.account_exists(b));

    s.add_to_balance(a, 0);
    EXPECT_TRUE(s.account_exists(a));
    s.destruct_touched_dead();
    s.destruct_suicides();
    EXPECT_FALSE(s.account_exists(a));

    s.subtract_from_balance(a, 0);
    EXPECT_TRUE(s.account_exists(a));
    s.destruct_touched_dead();
    s.destruct_suicides();
    EXPECT_FALSE(s.account_exists(a));
}

// Storage
TYPED_TEST(StateTest, access_storage)
{
    BlockState bs{this->db};

    State s{bs};
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
    BlockState bs{this->db};
    this->db.commit(
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
        Code{});

    State s{bs};
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
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key2, {bytes32_t{}, value2}}}}},
            {b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});

    State s{bs};
    EXPECT_TRUE(s.account_exists(a));
    EXPECT_EQ(s.set_storage(a, key2, value3), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.get_storage(a, key2), value3);
}

TYPED_TEST(StateTest, set_storage_deleted)
{
    BlockState bs{this->db};

    this->db.commit(
        StateDeltas{
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{});

    State s{bs};
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
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{{b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});

    State s{bs};
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
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key2, {bytes32_t{}, value2}}}}},
            {b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});

    State s{bs};
    EXPECT_TRUE(s.account_exists(a));
    EXPECT_EQ(s.set_storage(a, key2, value3), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.get_storage(a, key2), value3);
    EXPECT_EQ(s.set_storage(a, key2, value1), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.get_storage(a, key2), value1);
}

TYPED_TEST(StateTest, set_storage_unchanged_assigned)
{
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key2, {bytes32_t{}, value2}}}}},
            {b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});

    State s{bs};
    EXPECT_TRUE(s.account_exists(a));
    EXPECT_EQ(s.set_storage(a, key2, value2), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.get_storage(a, key2), value2);
}

TYPED_TEST(StateTest, set_storage_added_deleted)
{
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{{b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});

    State s{bs};
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_EQ(s.set_storage(b, key1, value1), EVMC_STORAGE_ADDED);
    EXPECT_EQ(s.get_storage(b, key1), value1);
    EXPECT_EQ(s.set_storage(b, key1, null), EVMC_STORAGE_ADDED_DELETED);
    EXPECT_EQ(s.get_storage(b, key1), null);
}

TYPED_TEST(StateTest, set_storage_added_deleted_null)
{
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{{b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});

    State s{bs};
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_EQ(s.set_storage(b, key1, null), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.get_storage(b, key1), null);
    EXPECT_EQ(s.set_storage(b, key1, null), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.get_storage(b, key1), null);
}

TYPED_TEST(StateTest, set_storage_modify_delete)
{
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key2, {bytes32_t{}, value2}}}}}},
        Code{});

    State s{bs};
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_EQ(s.set_storage(b, key2, value1), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.get_storage(b, key2), value1);
    EXPECT_EQ(s.set_storage(b, key2, null), EVMC_STORAGE_MODIFIED_DELETED);
    EXPECT_EQ(s.get_storage(b, key2), null);
}

TYPED_TEST(StateTest, set_storage_delete_restored)
{
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key2, {bytes32_t{}, value2}}}}}},
        Code{});

    State s{bs};
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_EQ(s.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(s.get_storage(b, key2), null);
    EXPECT_EQ(s.set_storage(b, key2, value2), EVMC_STORAGE_DELETED_RESTORED);
    EXPECT_EQ(s.get_storage(b, key2), value2);
}

TYPED_TEST(StateTest, set_storage_modified_restored)
{
    BlockState bs{this->db};
    this->db.commit(
        StateDeltas{
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key2, {bytes32_t{}, value2}}}}}},
        Code{});

    State s{bs};
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_EQ(s.set_storage(b, key2, value1), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.get_storage(b, key2), value1);
    EXPECT_EQ(s.set_storage(b, key2, value2), EVMC_STORAGE_MODIFIED_RESTORED);
    EXPECT_EQ(s.get_storage(b, key2), value2);
}

// Code
TYPED_TEST(StateTest, get_code_size)
{
    BlockState bs{this->db};
    Account acct{.code_hash = code_hash1};
    this->db.commit(
        StateDeltas{{a, StateDelta{.account = {std::nullopt, acct}}}},
        Code{{code_hash1, code_analysis1}});

    State s{bs};
    EXPECT_EQ(s.get_code_size(a), code1.size());
}

TYPED_TEST(StateTest, copy_code)
{
    BlockState bs{this->db};
    Account acct_a{.code_hash = code_hash1};
    Account acct_b{.code_hash = code_hash2};

    this->db.commit(
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, acct_a}}},
            {b, StateDelta{.account = {std::nullopt, acct_b}}}},
        Code{{code_hash1, code_analysis1}, {code_hash2, code_analysis2}});

    static constexpr unsigned size{8};
    uint8_t buffer[size];

    State s{bs};

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

    BlockState bs{this->db};

    this->db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.code_hash = code_hash1}}}}},
        Code{{code_hash1, std::make_shared<CodeAnalysis>(analyze(contract))}});

    State s{bs};

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
    BlockState bs{this->db};

    State s{bs};
    s.create_contract(a);
    s.create_contract(b);
    s.set_code(a, code2);
    s.set_code(b, byte_string{});

    EXPECT_EQ(s.get_code(a)->executable_code, code2);
    EXPECT_EQ(s.get_code(b)->executable_code, byte_string{});
}

TYPED_TEST(StateTest, can_merge_same_account_different_storage)
{
    BlockState bs{this->db};

    this->db.commit(
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
        Code{});

    State as{bs};
    State cs{bs};

    EXPECT_TRUE(as.account_exists(b));
    EXPECT_EQ(as.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);

    EXPECT_TRUE(bs.can_merge(as));
    bs.merge(as);

    EXPECT_TRUE(cs.account_exists(b));
    EXPECT_EQ(cs.set_storage(b, key2, null), EVMC_STORAGE_DELETED);

    EXPECT_TRUE(bs.can_merge(cs));
    bs.merge(cs);
}

TYPED_TEST(StateTest, cant_merge_colliding_storage)
{
    BlockState bs{this->db};

    this->db.commit(
        StateDeltas{
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 40'000}},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{});

    State as{bs};
    State cs{bs};

    EXPECT_TRUE(as.account_exists(b));
    EXPECT_EQ(as.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);

    EXPECT_TRUE(cs.account_exists(b));
    EXPECT_EQ(cs.set_storage(b, key1, null), EVMC_STORAGE_DELETED);

    EXPECT_TRUE(bs.can_merge(as));
    bs.merge(as);

    EXPECT_FALSE(bs.can_merge(cs));

    // Need to rerun txn 1 - get new changset
    {
        State cs{bs};
        EXPECT_TRUE(cs.account_exists(b));
        EXPECT_EQ(cs.set_storage(b, key1, null), EVMC_STORAGE_DELETED);

        EXPECT_TRUE(bs.can_merge(cs));
        bs.merge(cs);
    }
}

TYPED_TEST(StateTest, merge_txn0_and_txn1)
{
    BlockState bs{this->db};

    this->db.commit(
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
        Code{});

    State as{bs};
    State cs{bs};

    EXPECT_TRUE(as.account_exists(b));
    EXPECT_EQ(as.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(as.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(as.set_storage(b, key2, value2), EVMC_STORAGE_DELETED_RESTORED);

    EXPECT_TRUE(bs.can_merge(as));
    bs.merge(as);

    EXPECT_TRUE(cs.account_exists(c));
    EXPECT_EQ(cs.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(cs.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_TRUE(cs.selfdestruct(c, a));
    cs.destruct_suicides();

    EXPECT_TRUE(bs.can_merge(cs));
    bs.merge(cs);
}

TYPED_TEST(StateTest, cant_merge_txn1_collision_need_to_rerun)
{
    BlockState bs{this->db};

    this->db.commit(
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
        Code{});

    State as{bs};
    State cs{bs};

    EXPECT_TRUE(as.account_exists(b));
    EXPECT_EQ(as.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(as.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(as.set_storage(b, key2, value2), EVMC_STORAGE_DELETED_RESTORED);

    EXPECT_TRUE(bs.can_merge(as));
    bs.merge(as);

    EXPECT_TRUE(cs.account_exists(c));
    EXPECT_TRUE(cs.account_exists(b));
    EXPECT_EQ(cs.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(cs.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_TRUE(cs.selfdestruct(c, b));
    cs.destruct_suicides();

    EXPECT_TRUE(bs.can_merge(cs));

    State ds{bs};

    EXPECT_TRUE(ds.account_exists(c));
    EXPECT_TRUE(ds.account_exists(b));
    EXPECT_EQ(ds.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(ds.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_TRUE(ds.selfdestruct(c, b));
    ds.destruct_suicides();

    EXPECT_TRUE(bs.can_merge(ds));
    bs.merge(ds);
}

TYPED_TEST(StateTest, commit_storage_and_account_together_regression)
{
    BlockState bs{this->db};
    State as{bs};

    as.create_contract(a);
    as.add_to_balance(a, 1);
    as.set_storage(a, key1, value1);

    bs.merge(as);
    bs.commit();

    EXPECT_TRUE(this->db.read_account(a).has_value());
    EXPECT_EQ(this->db.read_account(a).value().balance, 1u);
    EXPECT_EQ(this->db.read_storage(a, key1), value1);
}

TYPED_TEST(StateTest, set_and_then_clear_storage_in_same_commit)
{
    using namespace intx;
    BlockState bs{this->db};
    State as{bs};

    as.create_contract(a);
    EXPECT_EQ(as.set_storage(a, key1, value1), EVMC_STORAGE_ADDED);
    EXPECT_EQ(as.set_storage(a, key1, null), EVMC_STORAGE_ADDED_DELETED);
    bs.merge(as);
    bs.commit();

    EXPECT_EQ(this->db.read_storage(a, key1), monad::bytes32_t{});
}

TYPED_TEST(StateTest, commit_twice)
{
    this->db.commit(
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
        Code{});

    {
        // Block 0, Txn 0
        BlockState bs{this->db};
        State as{bs};
        EXPECT_TRUE(as.account_exists(b));
        as.add_to_balance(b, 42'000);
        as.set_nonce(b, 3);
        EXPECT_EQ(as.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(as.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(
            as.set_storage(b, key2, value2), EVMC_STORAGE_DELETED_RESTORED);
        EXPECT_TRUE(bs.can_merge(as));
        bs.merge(as);
        bs.commit();

        EXPECT_EQ(this->db.read_storage(b, key1), value2);
        EXPECT_EQ(this->db.read_storage(b, key2), value2);
    }
    {
        // Block 1, Txn 0
        BlockState bs{this->db};
        State cs{bs};
        EXPECT_TRUE(cs.account_exists(a));
        EXPECT_TRUE(cs.account_exists(c));
        EXPECT_EQ(cs.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(cs.set_storage(c, key2, value1), EVMC_STORAGE_MODIFIED);
        EXPECT_TRUE(cs.selfdestruct(c, a));
        cs.destruct_suicides();
        EXPECT_TRUE(bs.can_merge(cs));
        bs.merge(cs);
        bs.commit();

        EXPECT_EQ(this->db.read_storage(c, key1), monad::bytes32_t{});
        EXPECT_EQ(this->db.read_storage(c, key2), monad::bytes32_t{});
    }
}
