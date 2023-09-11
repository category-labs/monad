#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>

#include <monad/db/in_memory_trie_db.hpp>
#include <monad/db/rocks_trie_db.hpp>
#include <monad/state/state_changes.hpp>
#include <monad/state2/state.hpp>
#include <monad/test/make_db.hpp>

#include <gtest/gtest.h>
#include <unordered_map>

using namespace monad;
using namespace monad::state;

static constexpr auto a = 0x5353535353535353535353535353535353535353_address;
static constexpr auto b = 0xbebebebebebebebebebebebebebebebebebebebe_address;
static constexpr auto c = 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5_address;
static constexpr auto key1 =
    0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
static constexpr auto key2 =
    0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
static constexpr auto key3 =
    0x5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b_bytes32;
static constexpr auto value1 =
    0x0000000000000000000000000000000000000000000000000000000000000003_bytes32;
static constexpr auto value2 =
    0x0000000000000000000000000000000000000000000000000000000000000007_bytes32;
static constexpr auto value3 =
    0x000000000000000000000000000000000000000000000000000000000000000a_bytes32;
static constexpr auto null =
    0x0000000000000000000000000000000000000000000000000000000000000000_bytes32;
static constexpr auto hash1 =
    0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
static constexpr auto code_hash1 =
    0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
static constexpr auto code_hash2 =
    0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
static constexpr auto code1 =
    byte_string{0x65, 0x74, 0x68, 0x65, 0x72, 0x6d, 0x69};
static constexpr auto code2 =
    byte_string{0x6e, 0x65, 0x20, 0x2d, 0x20, 0x45, 0x55, 0x31, 0x34};

template <typename TDB>
struct StateTest : public testing::Test
{
};
using DBTypes = ::testing::Types<db::InMemoryTrieDB, db::RocksTrieDB>;
TYPED_TEST_SUITE(StateTest, DBTypes);

struct fakeBlockCache
{
    [[nodiscard]] bytes32_t get_block_hash(int64_t) const noexcept
    {
        return bytes32_t{};
    }
} block_cache;

using mutex_t = std::shared_mutex;

TYPED_TEST(StateTest, access_account)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 10'000}}}}},
        Code{});

    State s{bs, db, block_cache};

    EXPECT_EQ(s.access_account(a), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_account(a), EVMC_ACCESS_WARM);
    EXPECT_EQ(s.access_account(b), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_account(b), EVMC_ACCESS_WARM);
}

TYPED_TEST(StateTest, account_exists)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 10'000}}}}},
        Code{});

    State s{bs, db, block_cache};

    EXPECT_TRUE(s.account_exists(a));
    EXPECT_FALSE(s.account_exists(b));
}

TYPED_TEST(StateTest, create_account)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;

    State s{bs, db, block_cache};
    s.create_account(a);
    EXPECT_TRUE(s.account_exists(a));

    // allow pre-existing empty account
    EXPECT_FALSE(s.account_exists(b));
    s.create_account(b);
    EXPECT_TRUE(s.account_exists(b));
}

TYPED_TEST(StateTest, get_balance)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 10'000}}}}},
        Code{});

    State s{bs, db, block_cache};
    s.create_account(b);

    EXPECT_EQ(s.get_balance(a), bytes32_t{10'000});
    EXPECT_EQ(s.get_balance(b), bytes32_t{0});
    EXPECT_EQ(s.get_balance(c), bytes32_t{0});
}

TYPED_TEST(StateTest, set_balance)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, Account{.balance = 1}}}}},
        Code{});

    State s{bs, db, block_cache};
    s.create_account(b);
    s.set_balance(a, 10'000);
    s.set_balance(b, 20'000);

    EXPECT_EQ(s.get_balance(a), bytes32_t{10'000});
    EXPECT_EQ(s.get_balance(b), bytes32_t{20'000});
}

TYPED_TEST(StateTest, get_nonce)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, Account{.nonce = 2}}}}},
        Code{});

    State s{bs, db, block_cache};
    s.create_account(b);

    EXPECT_EQ(s.get_nonce(a), 2);
    EXPECT_EQ(s.get_nonce(b), 0);
    EXPECT_EQ(s.get_nonce(c), 0);
}

TYPED_TEST(StateTest, set_nonce)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;

    State s{bs, db, block_cache};
    s.create_account(b);
    s.set_nonce(b, 1);

    EXPECT_EQ(s.get_nonce(b), 1);
}

TYPED_TEST(StateTest, get_code_hash)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.code_hash = hash1}}}}},
        Code{});

    State s{bs, db, block_cache};
    s.create_account(b);

    EXPECT_EQ(s.get_code_hash(a), hash1);
    EXPECT_EQ(s.get_code_hash(b), NULL_HASH);
    EXPECT_EQ(s.get_code_hash(c), NULL_HASH);
}

TYPED_TEST(StateTest, set_code_hash)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;

    State s{bs, db, block_cache};
    s.create_account(b);
    s.set_code_hash(b, hash1);

    EXPECT_EQ(s.get_code_hash(b), hash1);
}

TYPED_TEST(StateTest, selfdestruct)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
        StateDeltas{
            {a,
             StateDelta{.account = {std::nullopt, Account{.balance = 18'000}}}},
            {c,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 38'000}}}}},
        Code{});

    State s{bs, db, block_cache};
    s.create_account(b);
    s.set_balance(b, 28'000);

    EXPECT_TRUE(s.selfdestruct(a, c));
    EXPECT_EQ(s.total_selfdestructs(), 1u);
    EXPECT_EQ(s.get_balance(a), bytes32_t{});
    EXPECT_EQ(s.get_balance(c), bytes32_t{56'000});
    EXPECT_FALSE(s.selfdestruct(a, c));

    EXPECT_TRUE(s.selfdestruct(b, c));
    EXPECT_EQ(s.total_selfdestructs(), 2u);
    EXPECT_EQ(s.get_balance(b), bytes32_t{});
    EXPECT_EQ(s.get_balance(c), bytes32_t{84'000});
    EXPECT_FALSE(s.selfdestruct(b, c));

    s.destruct_suicides();
    EXPECT_FALSE(s.account_exists(a));
    EXPECT_FALSE(s.account_exists(b));
}

TYPED_TEST(StateTest, selfdestruct_self)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 18'000}}}}},
        Code{});

    State s{bs, db, block_cache};

    EXPECT_TRUE(s.selfdestruct(a, a));
    EXPECT_EQ(s.total_selfdestructs(), 1u);
    EXPECT_EQ(s.get_balance(a), bytes32_t{});

    s.destruct_suicides();
    EXPECT_FALSE(s.account_exists(a));
}

TYPED_TEST(StateTest, destruct_touched_dead)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
        StateDeltas{
            {a,
             StateDelta{.account = {std::nullopt, Account{.balance = 10'000}}}},
            {b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});

    State s{bs, db, block_cache};
    EXPECT_TRUE(s.account_exists(a));
    s.destruct_touched_dead();
    s.destruct_suicides();
    EXPECT_TRUE(s.account_exists(a));
    EXPECT_TRUE(s.account_exists(b));

    s.set_balance(a, 0);
    s.destruct_touched_dead();
    s.destruct_suicides();

    EXPECT_FALSE(s.account_exists(a));
    EXPECT_FALSE(s.account_exists(b));
}

TYPED_TEST(StateTest, apply_award)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, Account{.balance = 100}}}},
            {b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});

    State s{bs, db, block_cache};
    s.add_txn_award(150);
    s.add_txn_award(225);
    s.apply_reward(a, 20'000 + s.gas_award());
    s.apply_reward(b, 10'000);

    EXPECT_EQ(s.get_balance(a), bytes32_t{20'475});
    EXPECT_EQ(s.get_balance(b), bytes32_t{10'000});
}

// Storage
TYPED_TEST(StateTest, access_storage)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;

    State s{bs, db, block_cache};
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
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
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

    State s{bs, db, block_cache};
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
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key2, {bytes32_t{}, value2}}}}},
            {b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});

    State s{bs, db, block_cache};
    EXPECT_TRUE(s.account_exists(a));
    EXPECT_EQ(s.set_storage(a, key2, value3), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.get_storage(a, key2), value3);
}

TYPED_TEST(StateTest, set_storage_deleted)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;

    db.commit(
        StateDeltas{
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{});

    State s{bs, db, block_cache};
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
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
        StateDeltas{{b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});

    State s{bs, db, block_cache};
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
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key2, {bytes32_t{}, value2}}}}},
            {b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});

    State s{bs, db, block_cache};
    EXPECT_TRUE(s.account_exists(a));
    EXPECT_EQ(s.set_storage(a, key2, value3), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.get_storage(a, key2), value3);
    EXPECT_EQ(s.set_storage(a, key2, value1), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.get_storage(a, key2), value1);
}

TYPED_TEST(StateTest, set_storage_unchanged_assigned)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key2, {bytes32_t{}, value2}}}}},
            {b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});

    State s{bs, db, block_cache};
    EXPECT_TRUE(s.account_exists(a));
    EXPECT_EQ(s.set_storage(a, key2, value2), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.get_storage(a, key2), value2);
}

TYPED_TEST(StateTest, set_storage_added_deleted)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
        StateDeltas{{b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});

    State s{bs, db, block_cache};
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_EQ(s.set_storage(b, key1, value1), EVMC_STORAGE_ADDED);
    EXPECT_EQ(s.get_storage(b, key1), value1);
    EXPECT_EQ(s.set_storage(b, key1, null), EVMC_STORAGE_ADDED_DELETED);
    EXPECT_EQ(s.get_storage(b, key1), null);
}

TYPED_TEST(StateTest, set_storage_added_deleted_null)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
        StateDeltas{{b, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});

    State s{bs, db, block_cache};
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_EQ(s.set_storage(b, key1, null), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.get_storage(b, key1), null);
    EXPECT_EQ(s.set_storage(b, key1, null), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.get_storage(b, key1), null);
}

TYPED_TEST(StateTest, set_storage_modify_delete)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
        StateDeltas{
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key2, {bytes32_t{}, value2}}}}}},
        Code{});

    State s{bs, db, block_cache};
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_EQ(s.set_storage(b, key2, value1), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.get_storage(b, key2), value1);
    EXPECT_EQ(s.set_storage(b, key2, null), EVMC_STORAGE_MODIFIED_DELETED);
    EXPECT_EQ(s.get_storage(b, key2), null);
}

TYPED_TEST(StateTest, set_storage_delete_restored)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
        StateDeltas{
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key2, {bytes32_t{}, value2}}}}}},
        Code{});

    State s{bs, db, block_cache};
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_EQ(s.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(s.get_storage(b, key2), null);
    EXPECT_EQ(s.set_storage(b, key2, value2), EVMC_STORAGE_DELETED_RESTORED);
    EXPECT_EQ(s.get_storage(b, key2), value2);
}

TYPED_TEST(StateTest, set_storage_modified_restored)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    db.commit(
        StateDeltas{
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{}},
                 .storage = {{key2, {bytes32_t{}, value2}}}}}},
        Code{});

    State s{bs, db, block_cache};
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_EQ(s.set_storage(b, key2, value1), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.get_storage(b, key2), value1);
    EXPECT_EQ(s.set_storage(b, key2, value2), EVMC_STORAGE_MODIFIED_RESTORED);
    EXPECT_EQ(s.get_storage(b, key2), value2);
}

// Code
TYPED_TEST(StateTest, get_code_size)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    Account acct{.code_hash = code_hash1};
    db.commit(
        StateDeltas{{a, StateDelta{.account = {std::nullopt, acct}}}},
        Code{{code_hash1, code1}});

    State s{bs, db, block_cache};
    EXPECT_EQ(s.get_code_size(a), code1.size());
}

TYPED_TEST(StateTest, copy_code)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    Account acct_a{.code_hash = code_hash1};
    Account acct_b{.code_hash = code_hash2};

    db.commit(
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, acct_a}}},
            {b, StateDelta{.account = {std::nullopt, acct_b}}}},
        Code{{code_hash1, code1}, {code_hash2, code2}});

    static constexpr unsigned size{8};
    uint8_t buffer[size];

    State s{bs, db, block_cache};

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

    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;

    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, Account{.code_hash = code_hash1}}}}},
        Code{{code_hash1, contract}});

    State s{bs, db, block_cache};

    {
        s.access_account(a);
        auto const c = s.get_code(a);
        EXPECT_EQ(c, contract);
    }
    { // non-existant account
        auto const c = s.get_code(b);
        EXPECT_EQ(c, byte_string{});
    }
}

TYPED_TEST(StateTest, set_code)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;

    State s{bs, db, block_cache};
    s.create_account(a);
    s.create_account(b);
    s.set_code(a, code2);
    s.set_code(b, byte_string{});

    EXPECT_EQ(s.get_code(a), code2);
    EXPECT_EQ(s.get_code(b), byte_string{});
}

TYPED_TEST(StateTest, can_merge_new_account)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;

    db.commit(
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

    State t{bs, db, block_cache};
    {
        State s{t};

        s.create_account(a);
        s.set_nonce(a, 1);
        s.set_balance(a, 38'000);
        s.set_code(a, code1);
        EXPECT_EQ(s.set_storage(a, key2, value1), EVMC_STORAGE_ADDED);
        EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_ADDED);
        EXPECT_EQ(s.get_code_size(a), code1.size());
        t.merge(s);
    }
}

TYPED_TEST(StateTest, can_merge_update)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;

    db.commit(
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

    State t{bs, db, block_cache};
    {
        State s{t};

        s.set_balance(b, 42'000);
        s.set_nonce(b, 3);
        EXPECT_EQ(s.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(s.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(
            s.set_storage(b, key2, value2), EVMC_STORAGE_DELETED_RESTORED);

        EXPECT_TRUE(s.account_exists(
            c)); // Need to access account somehow before storage accesses
        EXPECT_EQ(s.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(s.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_TRUE(s.selfdestruct(c, b));
        s.destruct_suicides();

        t.merge(s);
    }
}

TYPED_TEST(StateTest, can_merge_same_account_different_storage)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;

    db.commit(
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

    State as{bs, db, block_cache};
    State cs{bs, db, block_cache};

    EXPECT_TRUE(as.account_exists(b));
    EXPECT_EQ(as.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);

    EXPECT_TRUE(can_merge(bs.state, as.state_));
    merge(bs.state, as.state_);

    EXPECT_TRUE(cs.account_exists(b));
    EXPECT_EQ(cs.set_storage(b, key2, null), EVMC_STORAGE_DELETED);

    EXPECT_TRUE(can_merge(bs.state, cs.state_));
    merge(bs.state, cs.state_);
}

TYPED_TEST(StateTest, cant_merge_colliding_storage)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;

    db.commit(
        StateDeltas{
            {b,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 40'000}},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{});

    State as{bs, db, block_cache};
    State cs{bs, db, block_cache};

    EXPECT_TRUE(as.account_exists(b));
    EXPECT_EQ(as.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);

    EXPECT_TRUE(cs.account_exists(b));
    EXPECT_EQ(cs.set_storage(b, key1, null), EVMC_STORAGE_DELETED);

    EXPECT_TRUE(can_merge(bs.state, as.state_));
    merge(bs.state, as.state_);

    EXPECT_FALSE(can_merge(bs.state, cs.state_));

    // Need to rerun txn 1 - get new changset
    {
        State cs{bs, db, block_cache};
        EXPECT_TRUE(cs.account_exists(b));
        EXPECT_EQ(cs.set_storage(b, key1, null), EVMC_STORAGE_DELETED);

        EXPECT_TRUE(can_merge(bs.state, cs.state_));
        merge(bs.state, cs.state_);
    }
}

TYPED_TEST(StateTest, merge_txn0_and_txn1)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;

    db.commit(
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

    State as{bs, db, block_cache};
    State cs{bs, db, block_cache};

    EXPECT_TRUE(as.account_exists(b));
    EXPECT_EQ(as.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(as.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(as.set_storage(b, key2, value2), EVMC_STORAGE_DELETED_RESTORED);

    EXPECT_TRUE(can_merge(bs.state, as.state_));
    merge(bs.state, as.state_);

    EXPECT_TRUE(cs.account_exists(c));
    EXPECT_EQ(cs.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(cs.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_TRUE(cs.selfdestruct(c, a));
    cs.destruct_suicides();

    EXPECT_TRUE(can_merge(bs.state, cs.state_));
    merge(bs.state, cs.state_);
}

TYPED_TEST(StateTest, cant_merge_txn1_collision_need_to_rerun)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;

    db.commit(
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

    State as{bs, db, block_cache};
    State cs{bs, db, block_cache};

    EXPECT_TRUE(as.account_exists(b));
    EXPECT_EQ(as.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(as.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(as.set_storage(b, key2, value2), EVMC_STORAGE_DELETED_RESTORED);

    EXPECT_TRUE(can_merge(bs.state, as.state_));
    merge(bs.state, as.state_);

    EXPECT_TRUE(cs.account_exists(c));
    EXPECT_TRUE(cs.account_exists(b));
    EXPECT_EQ(cs.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(cs.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_TRUE(cs.selfdestruct(c, b));
    cs.destruct_suicides();

    EXPECT_TRUE(can_merge(bs.state, cs.state_));

    State ds{bs, db, block_cache};

    EXPECT_TRUE(ds.account_exists(c));
    EXPECT_TRUE(ds.account_exists(b));
    EXPECT_EQ(ds.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(ds.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_TRUE(ds.selfdestruct(c, b));
    ds.destruct_suicides();

    EXPECT_TRUE(can_merge(bs.state, ds.state_));
    merge(bs.state, ds.state_);
}

template <typename TDB>
struct TrieDBTest : public testing::Test
{
};
using TrieDBTypes = ::testing::Types<db::InMemoryTrieDB, db::RocksTrieDB>;
TYPED_TEST_SUITE(TrieDBTest, TrieDBTypes);

TYPED_TEST(TrieDBTest, commit_storage_and_account_together_regression)
{
    auto db = test::make_db<TypeParam>();
    BlockState<mutex_t> bs;
    State as{bs, db, block_cache};

    as.create_account(a);
    as.set_balance(a, 1);
    (void)as.set_storage(a, key1, value1);

    merge(bs.state, as.state_);
    db.commit(bs.state, bs.code);

    EXPECT_TRUE(db.read_account(a).has_value());
    EXPECT_EQ(db.read_account(a).value().balance, 1u);
    EXPECT_EQ(db.read_storage(a, 0u, key1), value1);
}

TYPED_TEST(TrieDBTest, set_and_then_clear_storage_in_same_commit)
{
    using namespace intx;
    auto db = test::make_db<db::InMemoryTrieDB>();
    BlockState<mutex_t> bs;
    State as{bs, db, block_cache};

    as.create_account(a);
    EXPECT_EQ(as.set_storage(a, key1, value1), EVMC_STORAGE_ADDED);
    EXPECT_EQ(as.set_storage(a, key1, null), EVMC_STORAGE_ADDED_DELETED);
    merge(bs.state, as.state_);
    db.commit(bs.state, bs.code);

    EXPECT_EQ(db.read_storage(a, 0u, key1), monad::bytes32_t{});
}

TYPED_TEST(StateTest, commit_twice)
{
    auto db = test::make_db<TypeParam>();

    db.commit(
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
        BlockState<mutex_t> bs;
        State as{bs, db, block_cache};
        EXPECT_TRUE(as.account_exists(b));
        as.set_balance(b, 42'000);
        as.set_nonce(b, 3);
        EXPECT_EQ(as.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(as.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(
            as.set_storage(b, key2, value2), EVMC_STORAGE_DELETED_RESTORED);
        EXPECT_TRUE(can_merge(bs.state, as.state_));
        merge(bs.state, as.state_);
        db.commit(bs.state, bs.code);

        EXPECT_EQ(db.read_storage(b, 0u, key1), value2);
        EXPECT_EQ(db.read_storage(b, 0u, key2), value2);
    }
    {
        // Block 1, Txn 0
        BlockState<mutex_t> bs;
        State cs{bs, db, block_cache};
        EXPECT_TRUE(cs.account_exists(a));
        EXPECT_TRUE(cs.account_exists(c));
        EXPECT_EQ(cs.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(cs.set_storage(c, key2, value1), EVMC_STORAGE_MODIFIED);
        EXPECT_TRUE(cs.selfdestruct(c, a));
        cs.destruct_suicides();
        EXPECT_TRUE(can_merge(bs.state, cs.state_));
        merge(bs.state, cs.state_);
        db.commit(bs.state, bs.code);

        EXPECT_EQ(db.read_storage(c, 0u, key1), monad::bytes32_t{});
        EXPECT_EQ(db.read_storage(c, 0u, key2), monad::bytes32_t{});
    }
}

TYPED_TEST(StateTest, commit_twice_apply_reward)
{
    auto db = test::make_db<TypeParam>();

    {
        // Block 0, Txn 0
        BlockState<mutex_t> bs;
        State as{bs, db, block_cache};
        as.add_txn_award(10);
        as.apply_reward(a, 100u + as.gas_award());
        EXPECT_TRUE(can_merge(bs.state, as.state_));
        merge(bs.state, as.state_);
        db.commit(bs.state, bs.code);
    }
    {
        // Block 1, Txn 0
        BlockState<mutex_t> bs;
        State cs{bs, db, block_cache};
        cs.add_txn_award(10);
        cs.apply_reward(b, 300);
        cs.apply_reward(a, 100 + cs.gas_award());
        EXPECT_TRUE(can_merge(bs.state, cs.state_));
        merge(bs.state, cs.state_);
        db.commit(bs.state, bs.code);
    }
    {
        BlockState<mutex_t> bs;
        State ds{bs, db, block_cache};
        EXPECT_TRUE(ds.account_exists(a));
        EXPECT_TRUE(ds.account_exists(b));
        EXPECT_EQ(ds.get_balance(a), bytes32_t{220});
        EXPECT_EQ(ds.get_balance(b), bytes32_t{300});
    }
}
