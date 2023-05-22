#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>

#include <monad/db/account_store.hpp>

#include <gtest/gtest.h>

#include <unordered_map>

using namespace monad;
using namespace monad::db;

static constexpr auto a = 0x5353535353535353535353535353535353535353_address;
static constexpr auto b = 0xbebebebebebebebebebebebebebebebebebebebe_address;
static constexpr auto c = 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5_address;
static constexpr auto d = 0xb5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5_address;
static constexpr auto e = 0xc5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5_address;
static constexpr auto f = 0xd5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5_address;
static constexpr auto hash1 =
    0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
static constexpr auto hash2 =
    0x5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b_bytes32;

using db_t = std::unordered_map<address_t, Account>;
using diff_t = AccountStore<std::unordered_map<address_t, Account>>::diff_t;

// AccountStore
TEST(AccountStore, account_exists)
{
    db_t db{};
    AccountStore s{db};
    db.insert({a, {}});
    db.insert({d, {}});

    s.merged_.emplace(b, Account{});
    s.merged_.emplace(d, diff_t{Account{}, std::nullopt});
    s.merged_[d].updated.reset();

    EXPECT_TRUE(s.account_exists(a));
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_FALSE(s.account_exists(c));
    EXPECT_FALSE(s.account_exists(d));
}

TEST(AccountStore, get_balance)
{
    db_t db{};
    db.insert({a, {.balance = 20'000}});
    AccountStore s{db};
    s.merged_.emplace(
        b, diff_t{std::nullopt, Account{.balance = 10'000}});

    EXPECT_EQ(s.get_balance(a), bytes32_t{20'000});
    EXPECT_EQ(s.get_balance(b), bytes32_t{10'000});
}

TEST(AccountStore, get_code_hash)
{
    db_t db{};
    db.insert({a, {.code_hash = hash1}});
    AccountStore s{db};
    s.merged_.emplace(
        b, diff_t{std::nullopt, Account{.code_hash = hash2}});

    EXPECT_EQ(s.get_code_hash(a), hash1);
    EXPECT_EQ(s.get_code_hash(b), hash2);
}

TEST(AccountStore, working_copy)
{
    db_t db{};
    db[a] = {.balance = 10'000};
    AccountStore as{db};

    auto bs = decltype(as)::WorkingCopy{as};
    auto cs = decltype(as)::WorkingCopy{as};

    bs.access_account(a);
    bs.set_balance(a, 20'000);

    cs.access_account(a);
    cs.set_balance(a, 30'000);

    EXPECT_EQ(as.get_balance(a), bytes32_t{10'000});
    EXPECT_EQ(bs.get_balance(a), bytes32_t{20'000});
    EXPECT_EQ(cs.get_balance(a), bytes32_t{30'000});
}

// AccountStoreWorkingCopy
TEST(AccountStoreWorkingCopy, account_exists)
{
    db_t db{};
    AccountStore s{db};
    db.insert({a, {}});
    db.insert({d, {}});

    auto bs = decltype(s)::WorkingCopy{s};

    bs.merged_.emplace(b, Account{});
    bs.merged_.emplace(d, diff_t{Account{}, std::nullopt});
    bs.merged_[d].updated.reset();
    bs.changed_.emplace(e, Account{});
    bs.changed_.emplace(f, diff_t{Account{}, std::nullopt});
    bs.changed_[f].updated.reset();

    EXPECT_TRUE(bs.account_exists(a));
    EXPECT_TRUE(bs.account_exists(b));
    EXPECT_TRUE(bs.account_exists(e));
    EXPECT_FALSE(bs.account_exists(c));
    EXPECT_FALSE(bs.account_exists(d));
    EXPECT_FALSE(bs.account_exists(f));
}

TEST(AccountStoreWorkingCopy, access_account)
{
    db_t db{};
    AccountStore s{db};
    db.insert({a, {}});
    db.insert({b, {}});

    auto bs = decltype(s)::WorkingCopy{s};

    EXPECT_EQ(bs.access_account(a), EVMC_ACCESS_COLD);
    EXPECT_EQ(bs.access_account(a), EVMC_ACCESS_WARM);
    EXPECT_EQ(bs.access_account(b), EVMC_ACCESS_COLD);
    EXPECT_EQ(bs.access_account(b), EVMC_ACCESS_WARM);
}

TEST(AccountStoreWorkingCopy, get_balance)
{
    db_t db{};
    db.insert({a, {.balance = 20'000}});
    AccountStore s{db};
    s.merged_.emplace(
        b, diff_t{std::nullopt, Account{.balance = 10'000}});

    auto bs = decltype(s)::WorkingCopy{s};

    bs.access_account(a);
    bs.access_account(b);

    EXPECT_EQ(bs.get_balance(a), bytes32_t{20'000});
    EXPECT_EQ(bs.get_balance(b), bytes32_t{10'000});
}

TEST(AccountStoreWorkingCopy, get_nonce)
{
    db_t db{};
    db.insert({a, {.nonce = 2}});
    AccountStore s{db};
    s.merged_.emplace(b, diff_t{std::nullopt, Account{.nonce = 1}});

    auto bs = decltype(s)::WorkingCopy{s};

    bs.access_account(a);
    bs.access_account(b);

    EXPECT_EQ(bs.get_nonce(a), 2);
    EXPECT_EQ(bs.get_nonce(b), 1);
}

TEST(AccountStoreWorkingCopy, get_code_hash)
{
    db_t db{};
    db.insert({a, {.code_hash = hash1}});
    AccountStore s{db};
    s.merged_.emplace(
        b, diff_t{std::nullopt, Account{.code_hash = hash2}});

    auto bs = decltype(s)::WorkingCopy{s};

    bs.access_account(a);
    bs.access_account(b);

    EXPECT_EQ(bs.get_code_hash(a), hash1);
    EXPECT_EQ(bs.get_code_hash(b), hash2);
}

TEST(AccountStoreWorkingCopy, create_account)
{
    db_t db{};
    AccountStore s{db};

    auto bs = decltype(s)::WorkingCopy{s};

    bs.create_contract(a);
    bs.set_balance(a, 38'000);
    bs.set_nonce(a, 2);

    EXPECT_EQ(bs.get_balance(a), bytes32_t{38'000});
    EXPECT_EQ(bs.get_nonce(a), 2);
}

TEST(AccountStoreWorkingCopy, selfdestruct)
{
    db_t db{};
    db.insert({a, {.balance = 18'000}});
    db.insert({c, {.balance = 38'000}});
    AccountStore s{db};
    s.merged_.emplace(
        b, diff_t{std::nullopt, Account{.balance = 28'000}});

    auto bs = decltype(s)::WorkingCopy{s};

    bs.access_account(a);
    bs.access_account(b);
    bs.access_account(c);

    bs.selfdestruct(a, c);
    EXPECT_EQ(bs.total_selfdestructs(), 1u);
    EXPECT_EQ(bs.get_balance(a), bytes32_t{});
    EXPECT_EQ(bs.get_balance(c), bytes32_t{56'000});

    bs.selfdestruct(b, c);
    EXPECT_EQ(bs.total_selfdestructs(), 2u);
    EXPECT_EQ(bs.get_balance(b), bytes32_t{});
    EXPECT_EQ(bs.get_balance(c), bytes32_t{84'000});

    bs.destruct_suicides();
    EXPECT_FALSE(bs.account_exists(a));
    EXPECT_FALSE(bs.account_exists(b));
}

TEST(AccountStoreWorkingCopy, destruct_touched_dead)
{
    db_t db{};
    db.insert({a, {.balance = 10'000}});
    db.insert({b, {}});
    AccountStore s{db};

    auto bs = decltype(s)::WorkingCopy{s};

    bs.create_contract(a);
    bs.set_balance(a, 38'000);
    bs.destruct_touched_dead();
    bs.destruct_suicides();
    EXPECT_TRUE(bs.account_exists(a));
    EXPECT_TRUE(bs.account_exists(b));

    bs.access_account(b);
    bs.set_balance(a, 0);
    bs.set_nonce(a, 0);
    bs.destruct_touched_dead();
    bs.destruct_suicides();

    EXPECT_FALSE(bs.account_exists(a));
    EXPECT_FALSE(bs.account_exists(b));
}

TEST(AccountStoreWorkingCopy, revert_touched)
{
    db_t db{};
    db.insert({a, {.balance = 10'000, .nonce = 2}});
    AccountStore s{db};

    auto bs = decltype(s)::WorkingCopy{s};

    bs.access_account(a);
    bs.set_balance(a, 15'000);
    bs.create_contract(b);
    bs.revert();
    EXPECT_FALSE(s.account_exists(b));

    bs.access_account(a);
    EXPECT_EQ(bs.get_balance(a), bytes32_t{10'000});
    EXPECT_FALSE(bs.account_exists(b));
}

TEST(AccountStore, can_merge_fresh)
{
    db_t db{};
    db[b] = {.balance = 40'000u};
    db[c] = {.balance = 50'000u};
    AccountStore t{db};

    auto s = decltype(t)::WorkingCopy{t};

    s.access_account(b);
    s.access_account(c);
    s.create_contract(a);
    s.set_nonce(a, 1);
    s.set_balance(a, 38'000);
    s.set_balance(b, 42'000);
    s.set_nonce(b, 3);
    s.selfdestruct(c, b);
    s.destruct_suicides();

    EXPECT_TRUE(t.can_merge(s));
}

TEST(AccountStore, can_merge_onto_merged)
{
    db_t db{};
    db[b] = {.balance = 40'000u};
    db[c] = {.balance = 50'000u};
    AccountStore t{db};
    t.merged_.emplace(a, diff_t{Account{.balance = 30'000}});
    t.merged_.emplace(b, diff_t{db[b], db[b]});
    t.merged_.emplace(
        c, diff_t{Account{.balance = 50'000}, std::nullopt});
    t.merged_[c].updated.reset();

    auto s = decltype(t)::WorkingCopy{t};

    s.access_account(a);
    s.access_account(b);
    s.create_contract(c);
    s.set_nonce(c, 1);
    s.set_balance(c, 38'000);
    s.set_balance(b, 42'000);
    s.set_nonce(b, 3);
    s.selfdestruct(a, b);
    s.destruct_suicides();

    EXPECT_TRUE(t.can_merge(s));
}

TEST(AccountStore, cant_merge_colliding_merge)
{
    db_t db{};
    db[a] = {.balance = 40'000u};
    AccountStore t{db};
    diff_t r{db[a], db[a]};
    r.updated.value().balance = 80'000;

    auto s = decltype(t)::WorkingCopy{t};

    s.access_account(a);
    s.set_balance(a, 80'000);

    t.merged_.emplace(a, r);

    EXPECT_FALSE(t.can_merge(s));
}

TEST(AccountStore, cant_merge_deleted_merge)
{
    db_t db{};
    db[a] = {.balance = 40'000u};
    AccountStore t{db};
    diff_t r{db[a], db[a]};
    r.updated.value().balance = 60'000;

    auto s = decltype(t)::WorkingCopy{t};

    s.access_account(a);
    s.set_balance(a, 80'000);

    t.merged_.emplace(a, r);
    t.merged_[a].updated.reset();

    EXPECT_FALSE(t.can_merge(s));
}

TEST(AccountStore, cant_merge_conflicting_adds)
{
    db_t db{};
    AccountStore t{db};
    diff_t r{std::nullopt, Account{.balance = 10'000, .nonce = 1}};

    auto s = decltype(t)::WorkingCopy{t};

    s.create_contract(a);
    s.set_nonce(a, 1);
    s.set_balance(a, 80'000);

    t.merged_.emplace(a, r);

    EXPECT_FALSE(t.can_merge(s));
}

TEST(AccountStore, cant_merge_conflicting_modifies)
{
    db_t db{};
    db[a] = {.balance = 40'000u};
    AccountStore t{db};
    diff_t r{db[a], db[a]};
    r.updated.value().balance = 80'000;

    auto s = decltype(t)::WorkingCopy{t};

    s.access_account(a);
    s.set_balance(a, 60'000);

    t.merged_.emplace(a, r);

    EXPECT_FALSE(t.can_merge(s));
}

TEST(AccountStore, cant_merge_conflicting_deleted)
{
    db_t db{};
    db[b] = {.balance = 10'000u, .nonce = 1};
    db[c] = {.balance = 40'000u, .nonce = 2};
    AccountStore t{db};
    diff_t r{db[c], db[c]};
    r.updated.reset();
    auto s = decltype(t)::WorkingCopy{t};

    s.access_account(b);
    s.access_account(c);
    s.selfdestruct(c, b);
    s.destruct_suicides();

    t.merged_.emplace(c, r);

    EXPECT_FALSE(t.can_merge(s));
}

TEST(AccountStore, merge_multiple_changes)
{
    db_t db{};
    db[b] = {.balance = 40'000u};
    db[c] = {.balance = 50'000u};
    AccountStore t{db};

    {
        auto s = decltype(t)::WorkingCopy{t};

        s.access_account(b);
        s.access_account(c);
        s.create_contract(a);
        s.set_nonce(a, 1);
        s.set_balance(a, 38'000);
        s.set_balance(b, 42'000);
        s.set_nonce(b, 3);
        s.selfdestruct(c, b);
        s.destruct_suicides();

        EXPECT_TRUE(t.can_merge(s));
        t.merge_changes(s);
        EXPECT_EQ(t.get_balance(a), bytes32_t{38'000});
        EXPECT_EQ(t.get_balance(b), bytes32_t{92'000});
        EXPECT_FALSE(t.account_exists(c));
    }
    {
        auto s = decltype(t)::WorkingCopy{t};

        s.access_account(b);
        s.create_contract(c);
        s.set_balance(c, 22'000);
        s.set_nonce(c, 1);
        s.set_balance(b, 48'000);
        s.set_nonce(b, 4);

        EXPECT_TRUE(t.can_merge(s));
        t.merge_changes(s);
        EXPECT_TRUE(t.account_exists(c));
        EXPECT_EQ(t.get_balance(b), bytes32_t{48'000});
        EXPECT_EQ(t.get_balance(c), bytes32_t{22'000});
    }
}

TEST(AccountStore, can_commit)
{
    db_t db{};
    db[b] = {.balance = 40'000u};
    db[c] = {.balance = 50'000u};
    AccountStore t{db};
    diff_t r{db[c], db[c]};
    r.updated.reset();

    t.merged_.emplace(a, Account{.balance = 30'000});
    t.merged_.emplace(b, diff_t{db[b], db[b]});
    t.merged_.emplace(c, r);

    EXPECT_TRUE(t.can_commit());
}

TEST(AccountStore, cant_commit_merged_new_different_than_stored)
{
    db_t db{};
    db[a] = {.balance = 40'000u};
    AccountStore t{db};
    t.merged_.emplace(a, diff_t{Account{.balance = 30'000}});

    EXPECT_FALSE(t.can_commit());
}

TEST(AccountStore, cant_commit_merged_different_than_stored_balance)
{
    db_t db{};
    db[a] = {.balance = 40'000u};
    AccountStore t{db};
    t.merged_.emplace(
        a, diff_t{Account{.balance = 30'000}, Account{.balance = 30'000}});

    EXPECT_FALSE(t.can_commit());
}

TEST(AccountStore, cant_commit_merged_different_than_stored_nonce)
{
    db_t db{};
    db[a] = {.balance = 40'000u};
    AccountStore t{db};
    t.merged_.emplace(
        a,
        diff_t{
            Account{.balance = 40'000, .nonce = 1},
            Account{.balance = 30'000}});

    EXPECT_FALSE(t.can_commit());
}

TEST(AccountStore, cant_commit_merged_different_than_stored_code_hash)
{
    db_t db{};
    db[a] = {.code_hash = hash1};
    AccountStore t{db};
    t.merged_.emplace(a, diff_t{Account{.code_hash = hash2}, Account{}});

    EXPECT_FALSE(t.can_commit());
}

TEST(AccountStore, cant_commit_deleted_isnt_stored)
{
    db_t db{};
    db[a] = {};
    AccountStore t{db};
    diff_t r{Account{.balance = 10'000}, std::nullopt};
    r.updated.reset();

    t.merged_.emplace(b, r);
    EXPECT_FALSE(t.can_commit());
}

TEST(AccountStore, can_commit_multiple)
{
    db_t db{};
    db[b] = {.balance = 40'000u};
    db[c] = {.balance = 50'000u};
    db[d] = {.balance = 60'000u};
    AccountStore t{db};

    {
        auto s = decltype(t)::WorkingCopy{t};

        s.access_account(b);
        s.access_account(c);
        s.create_contract(a);
        s.set_nonce(a, 1);
        s.set_balance(a, 38'000);
        s.set_balance(b, 42'000);
        s.set_nonce(b, 3);
        s.selfdestruct(c, b);
        s.destruct_suicides();

        EXPECT_TRUE(t.can_merge(s));
        t.merge_changes(s);
    }
    {
        auto s = decltype(t)::WorkingCopy{t};

        s.access_account(a);
        s.access_account(b);
        s.access_account(d);
        s.create_contract(c);
        s.set_balance(c, 22'000);
        s.set_nonce(c, 1);
        s.set_balance(b, 48'000);
        s.set_nonce(b, 4);
        s.selfdestruct(d, a);
        s.destruct_suicides();

        EXPECT_TRUE(t.can_merge(s));
        t.merge_changes(s);
    }

    EXPECT_TRUE(t.can_commit());
    t.commit_all_merged();

    EXPECT_TRUE(db.contains(a));
    EXPECT_EQ(db[a].balance, 98'000);
    EXPECT_EQ(db[a].nonce, 1);
    EXPECT_EQ(db[b].balance, 48'000);
    EXPECT_EQ(db[b].nonce, 4);
    EXPECT_EQ(db[c].balance, 22'000);
    EXPECT_EQ(db[c].nonce, 1);
    EXPECT_FALSE(db.contains(d));
}
