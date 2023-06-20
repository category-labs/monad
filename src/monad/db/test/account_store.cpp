#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>

#include <monad/db/account_store.hpp>
#include <monad/db/trie_db.hpp>

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

template <typename TDB>
struct AccountStoreTest : public testing::Test
{
};
using DBTypes =
    ::testing::Types<InMemoryDB, RocksDB, InMemoryTrieDB, RocksTrieDB>;
TYPED_TEST_SUITE(AccountStoreTest, DBTypes);

using diff_t = AccountStore<std::unordered_map<address_t, Account>>::diff_t;

// AccountStore
TYPED_TEST(AccountStoreTest, account_exists)
{
    TypeParam db{};
    AccountStore s{db};
    db.create(a, {});
    db.create(d, {});
    db.commit();

    s.merged_.emplace(b, Account{});
    s.merged_.emplace(d, diff_t{Account{}, std::nullopt});
    s.merged_[d].updated.reset();

    EXPECT_TRUE(s.account_exists(a));
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_FALSE(s.account_exists(c));
    EXPECT_FALSE(s.account_exists(d));
}

TYPED_TEST(AccountStoreTest, get_balance)
{
    TypeParam db{};
    db.create(a, {.balance = 20'000});
    db.commit();
    AccountStore s{db};
    s.merged_.emplace(
        b, diff_t{std::nullopt, Account{.balance = 10'000}});

    EXPECT_EQ(s.get_balance(a), bytes32_t{20'000});
    EXPECT_EQ(s.get_balance(b), bytes32_t{10'000});
}

TYPED_TEST(AccountStoreTest, get_code_hash)
{
    TypeParam db{};
    db.create(a, {.code_hash = hash1});
    db.commit();
    AccountStore s{db};
    s.merged_.emplace(
        b, diff_t{std::nullopt, Account{.code_hash = hash2}});

    EXPECT_EQ(s.get_code_hash(a), hash1);
    EXPECT_EQ(s.get_code_hash(b), hash2);
}

TYPED_TEST(AccountStoreTest, working_copy)
{
    TypeParam db{};
    db.create(a, {.balance = 10'000});
    db.commit();
    AccountStore as{db};

    auto bs = typename decltype(as)::WorkingCopy{as};
    auto cs = typename decltype(as)::WorkingCopy{as};

    bs.access_account(a);
    bs.set_balance(a, 20'000);

    cs.access_account(a);
    cs.set_balance(a, 30'000);

    EXPECT_EQ(as.get_balance(a), bytes32_t{10'000});
    EXPECT_EQ(bs.get_balance(a), bytes32_t{20'000});
    EXPECT_EQ(cs.get_balance(a), bytes32_t{30'000});
}

// AccountStoreWorkingCopy
TYPED_TEST(AccountStoreTest, account_exists_working_copy)
{
    TypeParam db{};
    AccountStore s{db};
    db.create(a, {});
    db.create(d, {});
    db.commit();

    auto bs = typename decltype(s)::WorkingCopy{s};

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

TYPED_TEST(AccountStoreTest, access_account_working_copy)
{
    TypeParam db{};
    AccountStore s{db};
    db.create(a, {});
    db.create(b, {});
    db.commit();

    auto bs = typename decltype(s)::WorkingCopy{s};

    EXPECT_EQ(bs.access_account(a), EVMC_ACCESS_COLD);
    EXPECT_EQ(bs.access_account(a), EVMC_ACCESS_WARM);
    EXPECT_EQ(bs.access_account(b), EVMC_ACCESS_COLD);
    EXPECT_EQ(bs.access_account(b), EVMC_ACCESS_WARM);
}

TYPED_TEST(AccountStoreTest, get_balance_working_copy)
{
    TypeParam db{};
    db.create(a, {.balance = 20'000});
    db.commit();

    AccountStore s{db};
    s.merged_.emplace(
        b, diff_t{std::nullopt, Account{.balance = 10'000}});

    auto bs = typename decltype(s)::WorkingCopy{s};

    bs.access_account(a);
    bs.access_account(b);

    EXPECT_EQ(bs.get_balance(a), bytes32_t{20'000});
    EXPECT_EQ(bs.get_balance(b), bytes32_t{10'000});
}

TYPED_TEST(AccountStoreTest, get_nonce_working_copy)
{
    TypeParam db{};
    db.create(a, {.nonce = 2});
    db.commit();

    AccountStore s{db};
    s.merged_.emplace(b, diff_t{std::nullopt, Account{.nonce = 1}});

    auto bs = typename decltype(s)::WorkingCopy{s};

    bs.access_account(a);
    bs.access_account(b);

    EXPECT_EQ(bs.get_nonce(a), 2);
    EXPECT_EQ(bs.get_nonce(b), 1);
}

TYPED_TEST(AccountStoreTest, get_code_hash_working_copy)
{
    TypeParam db{};
    db.create(a, {.code_hash = hash1});
    db.commit();

    AccountStore s{db};
    s.merged_.emplace(
        b, diff_t{std::nullopt, Account{.code_hash = hash2}});

    auto bs = typename decltype(s)::WorkingCopy{s};

    bs.access_account(a);
    bs.access_account(b);

    EXPECT_EQ(bs.get_code_hash(a), hash1);
    EXPECT_EQ(bs.get_code_hash(b), hash2);
}

TYPED_TEST(AccountStoreTest, create_account_working_copy)
{
    TypeParam db{};
    AccountStore s{db};

    auto bs = typename decltype(s)::WorkingCopy{s};

    bs.create_contract(a);
    bs.set_balance(a, 38'000);
    bs.set_nonce(a, 2);

    EXPECT_EQ(bs.get_balance(a), bytes32_t{38'000});
    EXPECT_EQ(bs.get_nonce(a), 2);
}

TYPED_TEST(AccountStoreTest, selfdestruct_working_copy)
{
    TypeParam db{};
    db.create(a, {.balance = 18'000});
    db.create(c, {.balance = 38'000});
    db.commit();

    AccountStore s{db};
    s.merged_.emplace(
        b, diff_t{std::nullopt, Account{.balance = 28'000}});

    auto bs = typename decltype(s)::WorkingCopy{s};

    bs.access_account(a);
    bs.access_account(b);
    bs.access_account(c);

    EXPECT_TRUE(bs.selfdestruct(a, c));
    EXPECT_EQ(bs.total_selfdestructs(), 1u);
    EXPECT_EQ(bs.get_balance(a), bytes32_t{});
    EXPECT_EQ(bs.get_balance(c), bytes32_t{56'000});
    EXPECT_FALSE(bs.selfdestruct(a, c));

    EXPECT_TRUE(bs.selfdestruct(b, c));
    EXPECT_EQ(bs.total_selfdestructs(), 2u);
    EXPECT_EQ(bs.get_balance(b), bytes32_t{});
    EXPECT_EQ(bs.get_balance(c), bytes32_t{84'000});
    EXPECT_FALSE(bs.selfdestruct(b, c));

    bs.destruct_suicides();
    EXPECT_FALSE(bs.account_exists(a));
    EXPECT_FALSE(bs.account_exists(b));
}

TYPED_TEST(AccountStoreTest, destruct_touched_dead_working_copy)
{
    TypeParam db{};
    db.create(a, {.balance = 10'000});
    db.create(b, {});
    db.commit();

    AccountStore s{db};

    auto bs = typename decltype(s)::WorkingCopy{s};

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

TYPED_TEST(AccountStoreTest, revert_touched_working_copy)
{
    TypeParam db{};
    db.create(a, {.balance = 10'000, .nonce = 2});
    db.commit();

    AccountStore s{db};

    auto bs = typename decltype(s)::WorkingCopy{s};

    bs.access_account(a);
    bs.set_balance(a, 15'000);
    bs.create_contract(b);
    bs.revert();
    EXPECT_FALSE(s.account_exists(b));

    bs.access_account(a);
    EXPECT_EQ(bs.get_balance(a), bytes32_t{10'000});
    EXPECT_FALSE(bs.account_exists(b));
}

TYPED_TEST(AccountStoreTest, can_merge_fresh)
{
    TypeParam db{};
    db.create(b, {.balance = 40'000u});
    db.create(c, {.balance = 50'000u});
    db.commit();

    AccountStore t{db};

    auto s = typename decltype(t)::WorkingCopy{t};

    s.access_account(b);
    s.access_account(c);
    s.create_contract(a);
    s.set_nonce(a, 1);
    s.set_balance(a, 38'000);
    s.set_balance(b, 42'000);
    s.set_nonce(b, 3);
    (void)s.selfdestruct(c, b);
    s.destruct_suicides();

    EXPECT_TRUE(t.can_merge(s));
}

TYPED_TEST(AccountStoreTest, can_merge_onto_merged)
{
    TypeParam db{};
    db.create(b, {.balance = 40'000u});
    db.create(c, {.balance = 50'000u});
    db.commit();

    AccountStore t{db};
    t.merged_.emplace(a, diff_t{Account{.balance = 30'000}});
    t.merged_.emplace(b, diff_t{db.at(b), db.at(b)});
    t.merged_.emplace(
        c, diff_t{Account{.balance = 50'000}, std::nullopt});
    t.merged_[c].updated.reset();

    auto s = typename decltype(t)::WorkingCopy{t};

    s.access_account(a);
    s.access_account(b);
    s.create_contract(c);
    s.set_nonce(c, 1);
    s.set_balance(c, 38'000);
    s.set_balance(b, 42'000);
    s.set_nonce(b, 3);
    (void)s.selfdestruct(a, b);
    s.destruct_suicides();

    EXPECT_TRUE(t.can_merge(s));
}

TYPED_TEST(AccountStoreTest, cant_merge_colliding_merge)
{
    TypeParam db{};
    db.create(a, {.balance = 40'000u});
    db.commit();

    AccountStore t{db};
    diff_t r{db.at(a), db.at(a)};
    r.updated.value().balance = 80'000;

    auto s = typename decltype(t)::WorkingCopy{t};

    s.access_account(a);
    s.set_balance(a, 80'000);

    t.merged_.emplace(a, r);

    EXPECT_FALSE(t.can_merge(s));
}

TYPED_TEST(AccountStoreTest, cant_merge_deleted_merge)
{
    TypeParam db{};
    db.create(a, {.balance = 40'000u});
    db.commit();

    AccountStore t{db};
    diff_t r{db.at(a), db.at(a)};
    r.updated.value().balance = 60'000;

    auto s = typename decltype(t)::WorkingCopy{t};

    s.access_account(a);
    s.set_balance(a, 80'000);

    t.merged_.emplace(a, r);
    t.merged_[a].updated.reset();

    EXPECT_FALSE(t.can_merge(s));
}

TYPED_TEST(AccountStoreTest, cant_merge_conflicting_adds)
{
    TypeParam db{};
    AccountStore t{db};
    diff_t r{std::nullopt, Account{.balance = 10'000, .nonce = 1}};

    auto s = typename decltype(t)::WorkingCopy{t};

    s.create_contract(a);
    s.set_nonce(a, 1);
    s.set_balance(a, 80'000);

    t.merged_.emplace(a, r);

    EXPECT_FALSE(t.can_merge(s));
}

TYPED_TEST(AccountStoreTest, cant_merge_conflicting_modifies)
{
    TypeParam db{};
    db.create(a, {.balance = 40'000u});
    db.commit();

    AccountStore t{db};
    diff_t r{db.at(a), db.at(a)};
    r.updated.value().balance = 80'000;

    auto s = typename decltype(t)::WorkingCopy{t};

    s.access_account(a);
    s.set_balance(a, 60'000);

    t.merged_.emplace(a, r);

    EXPECT_FALSE(t.can_merge(s));
}

TYPED_TEST(AccountStoreTest, cant_merge_conflicting_deleted)
{
    TypeParam db{};
    db.create(b, {.balance = 10'000u, .nonce = 1});
    db.create(c, {.balance = 40'000u, .nonce = 2});
    db.commit();

    AccountStore t{db};
    diff_t r{db.at(c), db.at(c)};
    r.updated.reset();
    auto s = typename decltype(t)::WorkingCopy{t};

    s.access_account(b);
    s.access_account(c);
    (void)s.selfdestruct(c, b);
    s.destruct_suicides();

    t.merged_.emplace(c, r);

    EXPECT_FALSE(t.can_merge(s));
}

TYPED_TEST(AccountStoreTest, merge_multiple_changes)
{
    TypeParam db{};
    db.create(b, {.balance = 40'000u});
    db.create(c, {.balance = 50'000u});
    db.commit();

    AccountStore t{db};

    {
        auto s = typename decltype(t)::WorkingCopy{t};

        s.access_account(b);
        s.access_account(c);
        s.create_contract(a);
        s.set_nonce(a, 1);
        s.set_balance(a, 38'000);
        s.set_balance(b, 42'000);
        s.set_nonce(b, 3);
        (void)s.selfdestruct(c, b);
        s.destruct_suicides();

        EXPECT_TRUE(t.can_merge(s));
        t.merge_changes(s);
        EXPECT_EQ(t.get_balance(a), bytes32_t{38'000});
        EXPECT_EQ(t.get_balance(b), bytes32_t{92'000});
        EXPECT_FALSE(t.account_exists(c));
    }
    {
        auto s = typename decltype(t)::WorkingCopy{t};

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

TYPED_TEST(AccountStoreTest, can_commit)
{
    TypeParam db{};
    db.create(b, {.balance = 40'000u});
    db.create(c, {.balance = 50'000u});
    db.commit();
    AccountStore t{db};
    diff_t r{db.at(c), db.at(c)};
    r.updated.reset();

    t.merged_.emplace(a, Account{.balance = 30'000});
    t.merged_.emplace(b, diff_t{db.at(b), db.at(b)});
    t.merged_.emplace(c, r);

    EXPECT_TRUE(t.can_commit());
}

TYPED_TEST(AccountStoreTest, cant_commit_merged_new_different_than_stored)
{
    TypeParam db{};
    db.create(a, {.balance = 40'000u});
    db.commit();
    AccountStore t{db};
    t.merged_.emplace(a, diff_t{Account{.balance = 30'000}});

    EXPECT_FALSE(t.can_commit());
}

TYPED_TEST(AccountStoreTest, cant_commit_merged_different_than_stored_balance)
{
    TypeParam db{};
    db.create(a, {.balance = 40'000u});
    db.commit();
    AccountStore t{db};
    t.merged_.emplace(
        a, diff_t{Account{.balance = 30'000}, Account{.balance = 30'000}});

    EXPECT_FALSE(t.can_commit());
}

TYPED_TEST(AccountStoreTest, cant_commit_merged_different_than_stored_nonce)
{
    TypeParam db{};
    db.create(a, {.balance = 40'000u});
    db.commit();
    AccountStore t{db};
    t.merged_.emplace(
        a,
        diff_t{
            Account{.balance = 40'000, .nonce = 1},
            Account{.balance = 30'000}});

    EXPECT_FALSE(t.can_commit());
}

TYPED_TEST(AccountStoreTest, cant_commit_merged_different_than_stored_code_hash)
{
    TypeParam db{};
    db.create(a, {.code_hash = hash1});
    db.commit();
    AccountStore t{db};
    t.merged_.emplace(a, diff_t{Account{.code_hash = hash2}, Account{}});

    EXPECT_FALSE(t.can_commit());
}

TYPED_TEST(AccountStoreTest, cant_commit_deleted_isnt_stored)
{
    TypeParam db{};
    db.create(a, {});
    db.commit();
    AccountStore t{db};
    diff_t r{Account{.balance = 10'000}, std::nullopt};
    r.updated.reset();

    t.merged_.emplace(b, r);
    EXPECT_FALSE(t.can_commit());
}

TYPED_TEST(AccountStoreTest, can_commit_multiple)
{
    TypeParam db{};
    db.create(b, {.balance = 40'000u});
    db.create(c, {.balance = 50'000u});
    db.create(d, {.balance = 60'000u});
    db.commit();
    AccountStore t{db};

    {
        auto s = typename decltype(t)::WorkingCopy{t};

        s.access_account(b);
        s.access_account(c);
        s.create_contract(a);
        s.set_nonce(a, 1);
        s.set_balance(a, 38'000);
        s.set_balance(b, 42'000);
        s.set_nonce(b, 3);
        (void)s.selfdestruct(c, b);
        s.destruct_suicides();

        EXPECT_TRUE(t.can_merge(s));
        t.merge_changes(s);
    }
    {
        auto s = typename decltype(t)::WorkingCopy{t};

        s.access_account(a);
        s.access_account(b);
        s.access_account(d);
        s.create_contract(c);
        s.set_balance(c, 22'000);
        s.set_nonce(c, 1);
        s.set_balance(b, 48'000);
        s.set_nonce(b, 4);
        (void)s.selfdestruct(d, a);
        s.destruct_suicides();

        EXPECT_TRUE(t.can_merge(s));
        t.merge_changes(s);
    }

    EXPECT_TRUE(t.can_commit());
    t.commit_all_merged();

    EXPECT_TRUE(db.contains(a));
    EXPECT_EQ(db.at(a).balance, 98'000);
    EXPECT_EQ(db.at(a).nonce, 1);
    EXPECT_EQ(db.at(b).balance, 48'000);
    EXPECT_EQ(db.at(b).nonce, 4);
    EXPECT_EQ(db.at(c).balance, 22'000);
    EXPECT_EQ(db.at(c).nonce, 1);
    EXPECT_FALSE(db.contains(d));
}
