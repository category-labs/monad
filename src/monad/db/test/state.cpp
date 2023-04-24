#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>

#include <monad/db/account_state.hpp>
#include <monad/db/account_storage.hpp>
#include <monad/db/in_memory_state.hpp>

#include <gtest/gtest.h>

#include <unordered_map>

using namespace monad;
using namespace monad::db;

static constexpr auto a = 0x5353535353535353535353535353535353535353_address;
static constexpr auto b = 0xbebebebebebebebebebebebebebebebebebebebe_address;
static constexpr auto c = 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5_address;
// static constexpr auto d = 0xb5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5_address;
// static constexpr auto e = 0xc5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5_address;
// static constexpr auto f = 0xd5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5_address;
// static constexpr auto hash1 =
// 0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
// static constexpr auto hash2 =
// 0x5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b_bytes32;

static constexpr auto key1 =
    0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
static constexpr auto key2 =
    0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
// static constexpr auto key3 =
// 0x5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b_bytes32;
static constexpr auto value1 =
    0x0000000000000000000000000000000000000000000000000000000000000003_bytes32;
static constexpr auto value2 =
    0x0000000000000000000000000000000000000000000000000000000000000007_bytes32;
// static constexpr auto value3 =
// 0x000000000000000000000000000000000000000000000000000000000000000a_bytes32;
static constexpr auto null =
    0x0000000000000000000000000000000000000000000000000000000000000000_bytes32;

using account_store_t = std::unordered_map<address_t, Account>;
using account_storage_t = std::unordered_map<bytes32_t, bytes32_t>;
using account_storage_store_t =
    std::unordered_map<address_t, account_storage_t>;

TEST(State, get_working_copy)
{
    account_store_t account_db{};
    Accounts accounts{account_db};
    account_storage_store_t storage_db{};
    AccountStorage storage{storage_db};
    State as{accounts, storage};
    account_db[a] = {.balance = 10'000};

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

TEST(State, can_merge_fresh)
{
    account_store_t account_db{};
    Accounts accounts{account_db};
    account_storage_store_t storage_db{};
    AccountStorage storage{storage_db};
    State t{accounts, storage};

    account_db[b] = {.balance = 40'000u};
    account_db[c] = {.balance = 50'000u};
    storage_db[b].insert({key1, value1});
    storage_db[b].insert({key2, value2});
    storage_db[c].insert({key1, value1});
    storage_db[c].insert({key2, value2});

    auto s = t.get_working_copy(0);

    s.create_contract(a);
    s.set_nonce(a, 1);
    s.set_balance(a, 38'000);
    EXPECT_EQ(s.set_storage(a, key2, value1), EVMC_STORAGE_ADDED);
    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_ADDED);

    s.access_account(b);
    s.set_balance(b, 42'000);
    s.set_nonce(b, 3);
    EXPECT_EQ(s.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(s.set_storage(b, key2, value2), EVMC_STORAGE_DELETED_RESTORED);

    s.access_account(c);
    EXPECT_EQ(s.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(s.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
    s.selfdestruct(c, b);
    s.destruct_suicides();

    EXPECT_EQ(t.can_merge_changes(s), decltype(t)::MergeStatus::WILL_SUCCEED);
}

TEST(State, can_merge_same_account_different_storage)
{
    account_store_t account_db{};
    Accounts accounts{account_db};
    account_storage_store_t storage_db{};
    AccountStorage storage{storage_db};
    State t{accounts, storage};

    account_db[b] = {.balance = 40'000u};
    account_db[c] = {.balance = 50'000u};
    storage_db[b].insert({key1, value1});
    storage_db[b].insert({key2, value2});
    storage_db[c].insert({key1, value1});
    storage_db[c].insert({key2, value2});

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

TEST(State, cant_merge_colliding_storage)
{
    account_store_t account_db{};
    Accounts accounts{account_db};
    account_storage_store_t storage_db{};
    AccountStorage storage{storage_db};
    State t{accounts, storage};

    account_db[b] = {.balance = 40'000u};
    storage_db[b].insert({key1, value1});

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

TEST(State, merge_txn0_and_txn1)
{
    account_store_t account_db{};
    Accounts accounts{account_db};
    account_storage_store_t storage_db{};
    AccountStorage storage{storage_db};
    State t{accounts, storage};

    account_db[a] = {.balance = 30'000u};
    account_db[b] = {.balance = 40'000u};
    account_db[c] = {.balance = 50'000u};
    storage_db[b].insert({key1, value1});
    storage_db[b].insert({key2, value2});
    storage_db[c].insert({key1, value1});
    storage_db[c].insert({key2, value2});

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
    cs.selfdestruct(c, a);
    cs.destruct_suicides();

    EXPECT_EQ(t.can_merge_changes(cs), decltype(t)::MergeStatus::WILL_SUCCEED);
    t.merge_changes(cs);
}

TEST(State, cant_merge_txn1_collision_need_to_rerun)
{
    account_store_t account_db{};
    Accounts accounts{account_db};
    account_storage_store_t storage_db{};
    AccountStorage storage{storage_db};
    State t{accounts, storage};

    account_db[b] = {.balance = 40'000u};
    account_db[c] = {.balance = 50'000u};
    storage_db[b].insert({key1, value1});
    storage_db[b].insert({key2, value2});
    storage_db[c].insert({key1, value1});
    storage_db[c].insert({key2, value2});

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
    cs.selfdestruct(c, b);
    cs.destruct_suicides();

    EXPECT_EQ(
        t.can_merge_changes(cs), decltype(t)::MergeStatus::COLLISION_DETECTED);

    // Need to rerun txn 1 - get new working copy
    auto ds = t.get_working_copy(1);

    ds.access_account(b);
    ds.access_account(c);
    EXPECT_EQ(ds.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(ds.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
    ds.selfdestruct(c, b);
    ds.destruct_suicides();

    EXPECT_EQ(t.can_merge_changes(ds), decltype(t)::MergeStatus::WILL_SUCCEED);
    t.merge_changes(cs);
}

TEST(State, merge_txn1_try_again_merge_txn0_then_txn1)
{
    account_store_t account_db{};
    Accounts accounts{account_db};
    account_storage_store_t storage_db{};
    AccountStorage storage{storage_db};
    State t{accounts, storage};

    account_db[a] = {.balance = 30'000u};
    account_db[b] = {.balance = 40'000u};
    account_db[c] = {.balance = 50'000u};
    storage_db[b].insert({key1, value1});
    storage_db[b].insert({key2, value2});
    storage_db[c].insert({key1, value1});
    storage_db[c].insert({key2, value2});

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
        cs.selfdestruct(c, a);
        cs.destruct_suicides();
    }
    EXPECT_EQ(t.can_merge_changes(cs), decltype(t)::MergeStatus::TRY_LATER);
    EXPECT_EQ(t.can_merge_changes(bs), decltype(t)::MergeStatus::WILL_SUCCEED);
    t.merge_changes(bs);
    EXPECT_EQ(t.can_merge_changes(cs), decltype(t)::MergeStatus::WILL_SUCCEED);
    t.merge_changes(cs);
}

TEST(State, can_commit) {}

TEST(State, cant_commit_colliding_accounts) {}

TEST(State, cant_commit_colliding_storage) {}

TEST(State, commit) {}

TEST(State, commit_twice) {}
