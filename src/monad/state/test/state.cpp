#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>

#include <monad/db/trie_db.hpp>

#include <monad/state/account_state.hpp>
#include <monad/state/code_state.hpp>
#include <monad/state/state.hpp>
#include <monad/state/value_state.hpp>

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
static constexpr auto value1 =
    0x0000000000000000000000000000000000000000000000000000000000000003_bytes32;
static constexpr auto value2 =
    0x0000000000000000000000000000000000000000000000000000000000000007_bytes32;
static constexpr auto null =
    0x0000000000000000000000000000000000000000000000000000000000000000_bytes32;
static constexpr auto c1 =
    byte_string{0x65, 0x74, 0x68, 0x65, 0x72, 0x6d, 0x69};

template <typename TDB>
struct StateTest : public testing::Test
{
};
using DBTypes =
    ::testing::Types<db::InMemoryDB, db::RocksDB, db::InMemoryTrieDB, db::RocksTrieDB>;
TYPED_TEST_SUITE(StateTest, DBTypes);

using code_db_t = std::unordered_map<address_t, byte_string>;

struct fakeBlockCache {
   [[nodiscard]] bytes32_t get_block_hash(int64_t) const noexcept
   {
       return bytes32_t{};
   } 
} block_cache;

TYPED_TEST(StateTest, get_working_copy)
{
    TypeParam db;
    AccountState accounts{db};
    ValueState values{db};
    code_db_t code_db{};
    CodeState code{code_db};
    State as{accounts, values, code, block_cache};
    db.create(a, {.balance = 10'000});
    db.commit();

    [[maybe_unused]] auto bs = as.get_working_copy(0);
    [[maybe_unused]] auto cs = as.get_working_copy(1);

    bs.access_account(a);
    bs.set_balance(a, 20'000);

    cs.access_account(a);
    cs.set_balance(a, 30'000);

    EXPECT_TRUE(bs.account_exists(a));
    EXPECT_FALSE(bs.account_exists(b));
    EXPECT_TRUE(cs.account_exists(a));
    EXPECT_FALSE(cs.account_exists(b));
    EXPECT_EQ(bs.get_balance(a), bytes32_t{20'000});
    EXPECT_EQ(cs.get_balance(a), bytes32_t{30'000});
}

TYPED_TEST(StateTest, get_code)
{
    TypeParam db;
    AccountState accounts{db};
    ValueState values{db};
    code_db_t code_db{};
    CodeState code{code_db};
    State as{accounts, values, code, block_cache};
    byte_string const contract{0x60, 0x34, 0x00};
    db.create(a, {.balance = 10'000});
    code_db.emplace(a, contract);
    db.commit();

    [[maybe_unused]] auto bs = as.get_working_copy(0);

    bs.access_account(a);
    auto const c = bs.get_code(a);

    EXPECT_EQ(c, contract);
}

TYPED_TEST(StateTest, can_merge_fresh)
{
    TypeParam db;
    AccountState accounts{db};
    ValueState values{db};
    code_db_t code_db{};
    CodeState code{code_db};
    State t{accounts, values, code, block_cache};

    db.create(b, {.balance = 40'000u});
    db.create(c, {.balance = 50'000u});
    db.create(b, key1, value1);
    db.create(b, key2, value2);
    db.create(c, key1, value1);
    db.create(c, key2, value2);
    db.commit();

    auto s = t.get_working_copy(0);

    s.create_contract(a);
    s.set_nonce(a, 1);
    s.set_balance(a, 38'000);
    s.set_code(a, c1);
    EXPECT_EQ(s.set_storage(a, key2, value1), EVMC_STORAGE_ADDED);
    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_ADDED);
    EXPECT_EQ(s.get_code_size(a), c1.size());

    s.access_account(b);
    s.set_balance(b, 42'000);
    s.set_nonce(b, 3);
    EXPECT_EQ(s.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(s.set_storage(b, key2, value2), EVMC_STORAGE_DELETED_RESTORED);

    s.access_account(c);
    EXPECT_EQ(s.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(s.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_TRUE(s.selfdestruct(c, b));
    s.destruct_suicides();

    EXPECT_EQ(t.can_merge_changes(s), decltype(t)::MergeStatus::WILL_SUCCEED);
}

TYPED_TEST(StateTest, can_merge_same_account_different_storage)
{
    TypeParam db;
    AccountState accounts{db};
    ValueState values{db};
    code_db_t code_db{};
    CodeState code{code_db};
    State t{accounts, values, code, block_cache};

    db.create(b, {.balance = 40'000u});
    db.create(c, {.balance = 50'000u});
    db.create(b, key1, value1);
    db.create(b, key2, value2);
    db.create(c, key1, value1);
    db.create(c, key2, value2);
    db.commit();

    auto bs = t.get_working_copy(0);
    auto cs = t.get_working_copy(1);

    bs.access_account(b);
    EXPECT_EQ(bs.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);

    EXPECT_EQ(t.can_merge_changes(bs), decltype(t)::MergeStatus::WILL_SUCCEED);
    t.merge_changes(bs);

    cs.access_account(b);
    EXPECT_EQ(cs.set_storage(b, key2, null), EVMC_STORAGE_DELETED);

    EXPECT_EQ(t.can_merge_changes(cs), decltype(t)::MergeStatus::WILL_SUCCEED);
    t.merge_changes(cs);
}

TYPED_TEST(StateTest, cant_merge_colliding_storage)
{
    TypeParam db;
    AccountState accounts{db};
    ValueState values{db};
    code_db_t code_db{};
    CodeState code{code_db};
    State t{accounts, values, code, block_cache};

    db.create(b, {.balance = 40'000u});
    db.create(b, key1, value1);
    db.commit();

    auto bs = t.get_working_copy(0);
    auto cs = t.get_working_copy(1);

    {
        bs.access_account(b);
        EXPECT_EQ(bs.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);

        EXPECT_EQ(
            t.can_merge_changes(bs), decltype(t)::MergeStatus::WILL_SUCCEED);
        t.merge_changes(bs);
    }
    {
        cs.access_account(b);
        EXPECT_EQ(cs.set_storage(b, key1, null), EVMC_STORAGE_DELETED);

        EXPECT_EQ(
            t.can_merge_changes(cs),
            decltype(t)::MergeStatus::COLLISION_DETECTED);
    }

    // Need to rerun txn 1 - get new working copy
    auto ds = t.get_working_copy(1);

    ds.access_account(b);
    EXPECT_EQ(ds.set_storage(b, key1, null), EVMC_STORAGE_DELETED);

    EXPECT_EQ(t.can_merge_changes(ds), decltype(t)::MergeStatus::WILL_SUCCEED);
    t.merge_changes(ds);
}

TYPED_TEST(StateTest, merge_txn0_and_txn1)
{
    TypeParam db;
    AccountState accounts{db};
    ValueState values{db};
    code_db_t code_db{};
    CodeState code{code_db};
    State t{accounts, values, code, block_cache};

    db.create(a, {.balance = 30'000u});
    db.create(b, {.balance = 40'000u});
    db.create(c, {.balance = 50'000u});
    db.create(b, key1, value1);
    db.create(b, key2, value2);
    db.create(c, key1, value1);
    db.create(c, key2, value2);
    db.commit();

    auto bs = t.get_working_copy(0);
    auto cs = t.get_working_copy(1);

    bs.access_account(b);
    bs.set_balance(b, 42'000);
    bs.set_nonce(b, 3);
    EXPECT_EQ(bs.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(bs.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(bs.set_storage(b, key2, value2), EVMC_STORAGE_DELETED_RESTORED);

    EXPECT_EQ(t.can_merge_changes(bs), decltype(t)::MergeStatus::WILL_SUCCEED);
    t.merge_changes(bs);

    cs.access_account(a);
    cs.access_account(c);
    EXPECT_EQ(cs.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(cs.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_TRUE(cs.selfdestruct(c, a));
    cs.destruct_suicides();

    EXPECT_EQ(t.can_merge_changes(cs), decltype(t)::MergeStatus::WILL_SUCCEED);
    t.merge_changes(cs);
}

TYPED_TEST(StateTest, cant_merge_txn1_collision_need_to_rerun)
{
    TypeParam db;
    AccountState accounts{db};
    ValueState values{db};
    code_db_t code_db{};
    CodeState code{code_db};
    State t{accounts, values, code, block_cache};

    db.create(b, {.balance = 40'000u});
    db.create(c, {.balance = 50'000u});
    db.create(b, key1, value1);
    db.create(b, key2, value2);
    db.create(c, key1, value1);
    db.create(c, key2, value2);
    db.commit();

    auto bs = t.get_working_copy(0);
    auto cs = t.get_working_copy(1);

    bs.access_account(b);
    bs.set_balance(b, 42'000);
    bs.set_nonce(b, 3);
    EXPECT_EQ(bs.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(bs.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(bs.set_storage(b, key2, value2), EVMC_STORAGE_DELETED_RESTORED);

    EXPECT_EQ(t.can_merge_changes(bs), decltype(t)::MergeStatus::WILL_SUCCEED);
    t.merge_changes(bs);

    cs.access_account(b);
    cs.access_account(c);
    EXPECT_EQ(cs.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(cs.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_TRUE(cs.selfdestruct(c, b));
    cs.destruct_suicides();

    EXPECT_EQ(
        t.can_merge_changes(cs), decltype(t)::MergeStatus::COLLISION_DETECTED);

    // Need to rerun txn 1 - get new working copy
    auto ds = t.get_working_copy(1);

    ds.access_account(b);
    ds.access_account(c);
    EXPECT_EQ(ds.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(ds.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_TRUE(ds.selfdestruct(c, b));
    ds.destruct_suicides();

    EXPECT_EQ(t.can_merge_changes(ds), decltype(t)::MergeStatus::WILL_SUCCEED);
    t.merge_changes(ds);
}

TYPED_TEST(StateTest, merge_txn1_try_again_merge_txn0_then_txn1)
{
    TypeParam db;
    AccountState accounts{db};
    ValueState values{db};
    code_db_t code_db{};
    CodeState code{code_db};
    State t{accounts, values, code, block_cache};

    db.create(a, {.balance = 30'000u});
    db.create(b, {.balance = 40'000u});
    db.create(c, {.balance = 50'000u});
    db.create(b, key1, value1);
    db.create(b, key2, value2);
    db.create(c, key1, value1);
    db.create(c, key2, value2);
    db.commit();

    auto bs = t.get_working_copy(0);
    auto cs = t.get_working_copy(1);

    {
        // Txn 0
        bs.access_account(b);
        bs.set_balance(b, 42'000);
        bs.set_nonce(b, 3);
        EXPECT_EQ(bs.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(bs.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(
            bs.set_storage(b, key2, value2), EVMC_STORAGE_DELETED_RESTORED);
    }
    {
        // Txn 1
        cs.access_account(a);
        cs.access_account(c);
        EXPECT_EQ(cs.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(cs.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_TRUE(cs.selfdestruct(c, a));
        cs.destruct_suicides();
    }
    EXPECT_EQ(t.can_merge_changes(cs), decltype(t)::MergeStatus::TRY_LATER);
    EXPECT_EQ(t.can_merge_changes(bs), decltype(t)::MergeStatus::WILL_SUCCEED);
    t.merge_changes(bs);
    EXPECT_EQ(t.can_merge_changes(cs), decltype(t)::MergeStatus::WILL_SUCCEED);
    t.merge_changes(cs);
}

TYPED_TEST(StateTest, can_commit)
{
    TypeParam db;
    AccountState accounts{db};
    ValueState values{db};
    code_db_t code_db{};
    CodeState code{code_db};
    State t{accounts, values, code, block_cache};

    db.create(a, {.balance = 30'000u});
    db.create(b, {.balance = 40'000u});
    db.create(c, {.balance = 50'000u});
    db.create(b, key1, value1);
    db.create(b, key2, value2);
    db.create(c, key1, value1);
    db.create(c, key2, value2);
    db.commit();

    auto bs = t.get_working_copy(0);
    auto cs = t.get_working_copy(1);

    {
        // Txn 0
        bs.access_account(b);
        bs.set_balance(b, 42'000);
        bs.set_nonce(b, 3);
        EXPECT_EQ(bs.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(bs.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(
            bs.set_storage(b, key2, value2), EVMC_STORAGE_DELETED_RESTORED);
        EXPECT_EQ(
            t.can_merge_changes(bs), decltype(t)::MergeStatus::WILL_SUCCEED);
        t.merge_changes(bs);
    }
    {
        // Txn 1
        cs.access_account(a);
        cs.access_account(c);
        EXPECT_EQ(cs.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(cs.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_TRUE(cs.selfdestruct(c, a));
        cs.destruct_suicides();
        EXPECT_EQ(
            t.can_merge_changes(cs), decltype(t)::MergeStatus::WILL_SUCCEED);
        t.merge_changes(cs);
    }
    EXPECT_TRUE(t.can_commit());
}

TYPED_TEST(StateTest, commit_twice)
{
    TypeParam db;
    AccountState accounts{db};
    ValueState values{db};
    code_db_t code_db{};
    CodeState code{code_db};
    State t{accounts, values, code, block_cache};

    db.create(a, {.balance = 30'000u});
    db.create(b, {.balance = 40'000u});
    db.create(c, {.balance = 50'000u});
    db.create(b, key1, value1);
    db.create(b, key2, value2);
    db.create(c, key1, value1);
    db.create(c, key2, value2);
    db.commit();

    {
        // Block 0, Txn 0
        auto bs = t.get_working_copy(0);
        bs.access_account(b);
        bs.set_balance(b, 42'000);
        bs.set_nonce(b, 3);
        EXPECT_EQ(bs.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(bs.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(
            bs.set_storage(b, key2, value2), EVMC_STORAGE_DELETED_RESTORED);
        EXPECT_EQ(
            t.can_merge_changes(bs), decltype(t)::MergeStatus::WILL_SUCCEED);
        t.merge_changes(bs);
        EXPECT_TRUE(t.can_commit());
        t.commit();
    }
    {
        // Block 1, Txn 0
        auto cs = t.get_working_copy(0);
        cs.access_account(a);
        cs.access_account(c);
        EXPECT_EQ(cs.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(cs.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_TRUE(cs.selfdestruct(c, a));
        cs.destruct_suicides();
        EXPECT_EQ(
            t.can_merge_changes(cs), decltype(t)::MergeStatus::WILL_SUCCEED);
        t.merge_changes(cs);
        EXPECT_TRUE(t.can_commit());
        t.commit();
    }
}
