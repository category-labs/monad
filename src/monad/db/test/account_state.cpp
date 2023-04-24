#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>

#include <monad/db/account_state.hpp>

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

using store_t = std::unordered_map<address_t, Account>;

// Accounts
TEST(Accounts, account_exists)
{
    store_t db{};
    Accounts s{db};
    db.insert({a, {}});
    db.insert({d, {}});

    s.merged_.accounts_.emplace(std::make_pair(b, Account{}));
    s.merged_.accounts_.emplace(std::make_pair(d, diff<Account>{Account{}, {}}));
    s.merged_.accounts_[d].updated.reset();

    EXPECT_TRUE(s.account_exists(a));
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_FALSE(s.account_exists(c));
    EXPECT_FALSE(s.account_exists(d));
}

TEST(Accounts, get_balance)
{
    store_t db{};
    db.insert({a, {.balance = 20'000}});
    Accounts s{db};
    s.merged_.accounts_.insert({b, {std::nullopt, {.balance = 10'000}}});

    EXPECT_EQ(s.get_balance(a), bytes32_t{20'000});
    EXPECT_EQ(s.get_balance(b), bytes32_t{10'000});
}

TEST(Accounts, get_code_hash)
{
    store_t db{};
    db.insert({a, {.code_hash = hash1}});
    Accounts s{db};
    s.merged_.accounts_.insert({b, {std::nullopt, {.code_hash = hash2}}});

    EXPECT_EQ(s.get_code_hash(a), hash1);
    EXPECT_EQ(s.get_code_hash(b), hash2);
}

TEST(Accounts, get_working_copy)
{
    store_t db{};
    db[a] = {.balance = 10'000};
    Accounts as{db};

    auto bs = as.get_working_copy();
    auto cs = as.get_working_copy();

    bs.access_account(a);
    bs.set_balance(a, 20'000);

    cs.access_account(a);
    cs.set_balance(a, 30'000);

    EXPECT_EQ(as.get_balance(a), bytes32_t{10'000});
    EXPECT_EQ(bs.get_balance(a), bytes32_t{20'000});
    EXPECT_EQ(cs.get_balance(a), bytes32_t{30'000});
}

// AccountsWorkingCopy
TEST(AccountsWorkingCopy, account_exists)
{
    store_t db{};
    Accounts s{db};
    db.insert({a, {}});
    db.insert({d, {}});

    auto bs = s.get_working_copy();

    bs.merged_.accounts_.emplace(std::make_pair(b, Account{}));
    bs.merged_.accounts_.emplace(std::make_pair(d, diff<Account>{Account{}, {}}));
    bs.merged_.accounts_[d].updated.reset();
    bs.changed_.accounts_.emplace(std::make_pair(e, Account{}));
    bs.changed_.accounts_.emplace(std::make_pair(f, diff<Account>{Account{}, {}}));
    bs.changed_.accounts_[f].updated.reset();

    EXPECT_TRUE(bs.account_exists(a));
    EXPECT_TRUE(bs.account_exists(b));
    EXPECT_TRUE(bs.account_exists(e));
    EXPECT_FALSE(bs.account_exists(c));
    EXPECT_FALSE(bs.account_exists(d));
    EXPECT_FALSE(bs.account_exists(f));
}

TEST(AccountsWorkingCopy, access_account)
{
    store_t db{};
    Accounts s{db};
    db.insert({a, {}});
    db.insert({b, {}});

    auto bs = s.get_working_copy();

    EXPECT_EQ(bs.access_account(a), EVMC_ACCESS_COLD);
    EXPECT_EQ(bs.access_account(a), EVMC_ACCESS_WARM);
    EXPECT_EQ(bs.access_account(b), EVMC_ACCESS_COLD);
    EXPECT_EQ(bs.access_account(b), EVMC_ACCESS_WARM);
}

TEST(AccountsWorkingCopy, get_balance)
{
    store_t db{};
    db.insert({a, {.balance = 20'000}});
    Accounts s{db};
    s.merged_.accounts_.insert({b, {std::nullopt, {.balance = 10'000}}});

    auto bs = s.get_working_copy();

    bs.access_account(a);
    bs.access_account(b);

    EXPECT_EQ(bs.get_balance(a), bytes32_t{20'000});
    EXPECT_EQ(bs.get_balance(b), bytes32_t{10'000});
}

TEST(AccountsWorkingCopy, get_nonce)
{
    store_t db{};
    db.insert({a, {.nonce = 2}});
    Accounts s{db};
    s.merged_.accounts_.insert({b, {std::nullopt, {.nonce = 1}}});

    auto bs = s.get_working_copy();

    bs.access_account(a);
    bs.access_account(b);

    EXPECT_EQ(bs.get_nonce(a), 2);
    EXPECT_EQ(bs.get_nonce(b), 1);
}

TEST(AccountsWorkingCopy, get_code_hash)
{
    store_t db{};
    db.insert({a, {.code_hash = hash1}});
    Accounts s{db};
    s.merged_.accounts_.insert({b, {std::nullopt, {.code_hash = hash2}}});

    auto bs = s.get_working_copy();

    bs.access_account(a);
    bs.access_account(b);

    EXPECT_EQ(bs.get_code_hash(a), hash1);
    EXPECT_EQ(bs.get_code_hash(b), hash2);
}

TEST(AccountsWorkingCopy, create_account)
{
    store_t db{};
    Accounts s{db};

    auto bs = s.get_working_copy();

    bs.create_contract(a);
    bs.set_balance(a, 38'000);
    bs.set_nonce(a, 2);

    EXPECT_EQ(bs.get_balance(a), bytes32_t{38'000});
    EXPECT_EQ(bs.get_nonce(a), 2);
}

TEST(AccountsWorkingCopy, selfdestruct)
{
    store_t db{};
    db.insert({a, {.balance = 18'000}});
    db.insert({c, {.balance = 38'000}});
    Accounts s{db};
    s.merged_.accounts_.insert({b, {std::nullopt, {.balance = 28'000}}});

    auto bs = s.get_working_copy();

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

TEST(AccountsWorkingCopy, destruct_touched_dead)
{
    store_t db{};
    db.insert({a, {.balance = 10'000}});
    db.insert({b, {}});
    Accounts s{db};

    auto bs = s.get_working_copy();

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

TEST(AccountsWorkingCopy, revert_touched)
{
    store_t db{};
    db.insert({a, {.balance = 10'000, .nonce = 2}});
    Accounts s{db};

    auto bs = s.get_working_copy();

    bs.access_account(a);
    bs.set_balance(a, 15'000);
    bs.create_contract(b);
    bs.revert();
    EXPECT_FALSE(s.account_exists(b));

    bs.access_account(a);
    EXPECT_EQ(bs.get_balance(a), bytes32_t{10'000});
    EXPECT_FALSE(bs.account_exists(b));
}

// Merge WorkingCopy into Accounts
TEST(MergeChangesIntoAccounts, can_merge_fresh)
{
    store_t db{};
    db[b] = {.balance = 40'000u};
    db[c] = {.balance = 50'000u};
    Accounts t{db};

    auto s = t.get_working_copy();

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

TEST(MergeChangesIntoAccounts, can_merge_onto_merged)
{
    store_t db{};
    db[b] = {.balance = 40'000u};
    db[c] = {.balance = 50'000u};
    Accounts t{db};
    t.merged_.accounts_.emplace(std::make_pair(a, diff<Account>{Account{.balance = 30'000}}));
    t.merged_.accounts_.emplace(std::make_pair(b, diff<Account>{db[b], db[b]}));
    t.merged_.accounts_.emplace(std::make_pair(c, diff<Account>{Account{.balance = 50'000}, {}}));
    t.merged_.accounts_[c].updated.reset();

    auto s = t.get_working_copy();

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

TEST(MergeChangesIntoAccounts, cant_merge_colliding_merge)
{
    store_t db{};
    db[a] = {.balance = 40'000u};
    Accounts t{db};
    diff<Account> r{db[a], db[a]};
    r.updated.value().balance = 80'000;

    auto s = t.get_working_copy();

    s.access_account(a);
    s.set_balance(a, 80'000);

    t.merged_.accounts_.insert({a, r});

    EXPECT_FALSE(t.can_merge(s));
}

TEST(MergeChangesIntoAccounts, cant_merge_deleted_merge)
{
    store_t db{};
    db[a] = {.balance = 40'000u};
    Accounts t{db};
    diff<Account> r{db[a], db[a]};
    r.updated.value().balance = 60'000;

    auto s = t.get_working_copy();

    s.access_account(a);
    s.set_balance(a, 80'000);

    t.merged_.accounts_.emplace(std::make_pair(a, r));
    t.merged_.accounts_[a].updated.reset();

    EXPECT_FALSE(t.can_merge(s));
}

TEST(MergeChangesIntoAccounts, cant_merge_conflicting_adds)
{
    store_t db{};
    Accounts t{db};
    diff<Account> r{std::nullopt, {.balance = 10'000, .nonce = 1}};

    auto s = t.get_working_copy();

    s.create_contract(a);
    s.set_nonce(a, 1);
    s.set_balance(a, 80'000);

    t.merged_.accounts_.insert({a, r});

    EXPECT_FALSE(t.can_merge(s));
}

TEST(MergeChangesIntoAccounts, cant_merge_conflicting_modifies)
{
    store_t db{};
    db[a] = {.balance = 40'000u};
    Accounts t{db};
    diff<Account> r{db[a], db[a]};
    r.updated.value().balance = 80'000;

    auto s = t.get_working_copy();

    s.access_account(a);
    s.set_balance(a, 60'000);

    t.merged_.accounts_.insert({a, r});

    EXPECT_FALSE(t.can_merge(s));
}

TEST(MergeChangesIntoAccounts, cant_merge_conflicting_deleted)
{
    store_t db{};
    db[b] = {.balance = 10'000u, .nonce = 1};
    db[c] = {.balance = 40'000u, .nonce = 2};
    Accounts t{db};
    diff<Account> r{db[c], db[c]};
    r.updated.reset();
    auto s = t.get_working_copy();

    s.access_account(b);
    s.access_account(c);
    s.selfdestruct(c, b);
    s.destruct_suicides();

    t.merged_.accounts_.emplace(std::make_pair(c, r));

    EXPECT_FALSE(t.can_merge(s));
}

TEST(MergeChangesIntoAccounts, merge_multiple_changes)
{
    store_t db{};
    db[b] = {.balance = 40'000u};
    db[c] = {.balance = 50'000u};
    Accounts t{db};

    {
        auto s = t.get_working_copy();

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
        auto s = t.get_working_copy();

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

TEST(CommitAccountChanges, can_commit)
{
    store_t db{};
    db[b] = {.balance = 40'000u};
    db[c] = {.balance = 50'000u};
    Accounts t{db};
    diff<Account> r{db[c], db[c]};
    r.updated.reset();

    t.merged_.accounts_.insert(std::make_pair(a, Account{.balance = 30'000}));
    t.merged_.accounts_.insert({b, {db[b], db[b]}});
    t.merged_.accounts_.emplace(std::make_pair(c, r));

    EXPECT_TRUE(t.can_commit());
}

TEST(CommitAccountChanges, cant_commit_merged_new_different_than_stored)
{
    store_t db{};
    db[a] = {.balance = 40'000u};
    Accounts t{db};
    t.merged_.accounts_.insert({a, diff<Account>{{.balance = 30'000}}});

    EXPECT_FALSE(t.can_commit());
}

TEST(CommitAccountChanges, cant_commit_merged_different_than_stored_balance)
{
    store_t db{};
    db[a] = {.balance = 40'000u};
    Accounts t{db};
    t.merged_.accounts_.insert(
        {a, {Account{.balance = 30'000}, Account{.balance = 30'000}}});

    EXPECT_FALSE(t.can_commit());
}

TEST(CommitAccountChanges, cant_commit_merged_different_than_stored_nonce)
{
    store_t db{};
    db[a] = {.balance = 40'000u};
    Accounts t{db};
    t.merged_.accounts_.insert(
        {a, {Account{.balance = 40'000, .nonce = 1}, Account{.balance = 30'000}}});

    EXPECT_FALSE(t.can_commit());
}

TEST(CommitAccountChanges, cant_commit_merged_different_than_stored_code_hash)
{
    store_t db{};
    db[a] = {.code_hash = hash1};
    Accounts t{db};
    t.merged_.accounts_.insert(
        {a, {Account{.code_hash = hash2}, Account{}}});

    EXPECT_FALSE(t.can_commit());
}

TEST(CommitAccountChanges, cant_commit_deleted_isnt_stored)
{
    store_t db{};
    db[a] = {};
    Accounts t{db};
    diff<Account> r{{.balance = 10'000}, {}};
    r.updated.reset();

    t.merged_.accounts_.emplace(std::make_pair(b, r));
    EXPECT_FALSE(t.can_commit());
}

TEST(CommitAccountChanges, can_commit_multiple)
{
    store_t db{};
    db[b] = {.balance = 40'000u};
    db[c] = {.balance = 50'000u};
    db[d] = {.balance = 60'000u};
    Accounts t{db};

    {
        auto s = t.get_working_copy();

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
        auto s = t.get_working_copy();

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
