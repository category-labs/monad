#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>

#include <monad/db/in_memory_db.hpp>
#include <monad/db/in_memory_trie_db.hpp>
#include <monad/db/rocks_db.hpp>
#include <monad/db/rocks_trie_db.hpp>

#include <monad/state/account_state.hpp>
#include <monad/state/state_changes.hpp>

#include <monad/test/make_db.hpp>

#include <gtest/gtest.h>

#include <unordered_map>

using namespace monad;
using namespace monad::state;

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
struct AccountStateTest : public testing::Test
{
};
using DBTypes = ::testing::Types<
    db::InMemoryDB, db::RocksDB, db::InMemoryTrieDB, db::RocksTrieDB>;
TYPED_TEST_SUITE(AccountStateTest, DBTypes);

using diff_t = AccountState<std::unordered_map<address_t, Account>>::diff_t;

// AccountState
TYPED_TEST(AccountStateTest, account_exists)
{
    auto db = test::make_db<TypeParam>();
    AccountState s{db};
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}, {d, Account{}}},
        .storage_changes = {}});

    s.merged_.emplace(b, Account{});
    s.merged_.emplace(d, diff_t{Account{}, std::nullopt});
    s.merged_[d].updated.reset();

    EXPECT_TRUE(s.account_exists(a));
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_FALSE(s.account_exists(c));
    EXPECT_FALSE(s.account_exists(d));
}

TYPED_TEST(AccountStateTest, get_balance)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{.balance = 20'000}}},
        .storage_changes = {}});
    AccountState s{db};
    s.merged_.emplace(b, diff_t{std::nullopt, Account{.balance = 10'000}});

    EXPECT_EQ(s.get_balance(a), bytes32_t{20'000});
    EXPECT_EQ(s.get_balance(b), bytes32_t{10'000});
}

TYPED_TEST(AccountStateTest, apply_reward)
{
    auto db = test::make_db<TypeParam>();
    AccountState s{db};
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}}, .storage_changes = {}});

    s.merged_.emplace(b, Account{});
    s.merged_.emplace(c, diff_t{Account{}, Account{.balance = 10}});

    s.apply_reward(a, 1);
    s.apply_reward(b, 2);
    s.apply_reward(c, 3);
    s.apply_reward(d, 4);

    EXPECT_EQ(s.get_balance(a), bytes32_t{1});
    EXPECT_EQ(s.get_balance(b), bytes32_t{2});
    EXPECT_EQ(s.get_balance(c), bytes32_t{13});
    EXPECT_EQ(s.get_balance(d), bytes32_t{4});
}

TYPED_TEST(AccountStateTest, get_code_hash)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{.code_hash = hash1}}},
        .storage_changes = {}});
    AccountState s{db};
    s.merged_.emplace(b, diff_t{std::nullopt, Account{.code_hash = hash2}});

    EXPECT_EQ(s.get_code_hash(a), hash1);
    EXPECT_EQ(s.get_code_hash(b), hash2);
}

TYPED_TEST(AccountStateTest, changeset)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{.balance = 10'000}}},
        .storage_changes = {}});
    AccountState as{db};

    auto bs = typename decltype(as)::ChangeSet{as};
    auto cs = typename decltype(as)::ChangeSet{as};

    bs.access_account(a);
    bs.set_balance(a, 20'000);

    cs.access_account(a);
    cs.set_balance(a, 30'000);

    EXPECT_EQ(as.get_balance(a), bytes32_t{10'000});
    EXPECT_EQ(bs.get_balance(a), bytes32_t{20'000});
    EXPECT_EQ(cs.get_balance(a), bytes32_t{30'000});
}

// AccountStateChangeSet
TYPED_TEST(AccountStateTest, account_exists_changeset)
{
    auto db = test::make_db<TypeParam>();
    AccountState s{db};
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}, {d, Account{}}},
        .storage_changes = {}});

    auto bs = typename decltype(s)::ChangeSet{s};

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

TYPED_TEST(AccountStateTest, access_account_changeset)
{
    auto db = test::make_db<TypeParam>();
    AccountState s{db};
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}, {b, Account{}}},
        .storage_changes = {}});

    auto bs = typename decltype(s)::ChangeSet{s};

    EXPECT_EQ(bs.access_account(a), EVMC_ACCESS_COLD);
    EXPECT_EQ(bs.access_account(a), EVMC_ACCESS_WARM);
    EXPECT_EQ(bs.access_account(b), EVMC_ACCESS_COLD);
    EXPECT_EQ(bs.access_account(b), EVMC_ACCESS_WARM);
}

TYPED_TEST(AccountStateTest, get_balance_changeset)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{.balance = 20'000}}},
        .storage_changes = {}});

    AccountState s{db};
    s.merged_.emplace(b, diff_t{std::nullopt, Account{.balance = 10'000}});

    auto bs = typename decltype(s)::ChangeSet{s};

    bs.access_account(a);
    bs.access_account(b);

    EXPECT_EQ(bs.get_balance(a), bytes32_t{20'000});
    EXPECT_EQ(bs.get_balance(b), bytes32_t{10'000});
}

TYPED_TEST(AccountStateTest, get_nonce_changeset)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{.nonce = 2}}}, .storage_changes = {}});

    AccountState s{db};
    s.merged_.emplace(b, diff_t{std::nullopt, Account{.nonce = 1}});

    auto bs = typename decltype(s)::ChangeSet{s};

    bs.access_account(a);
    bs.access_account(b);

    EXPECT_EQ(bs.get_nonce(a), 2);
    EXPECT_EQ(bs.get_nonce(b), 1);
}

TYPED_TEST(AccountStateTest, get_code_hash_changeset)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{.code_hash = hash1}}},
        .storage_changes = {}});

    AccountState s{db};
    s.merged_.emplace(b, diff_t{std::nullopt, Account{.code_hash = hash2}});

    auto bs = typename decltype(s)::ChangeSet{s};

    bs.access_account(a);
    bs.access_account(b);

    EXPECT_EQ(bs.get_code_hash(a), hash1);
    EXPECT_EQ(bs.get_code_hash(b), hash2);
}

TYPED_TEST(AccountStateTest, create_account_changeset)
{
    auto db = test::make_db<TypeParam>();
    AccountState s{db};

    auto bs = typename decltype(s)::ChangeSet{s};

    bs.create_account(a);
    bs.set_balance(a, 38'000);
    bs.set_nonce(a, 2);

    EXPECT_EQ(bs.get_balance(a), bytes32_t{38'000});
    EXPECT_EQ(bs.get_nonce(a), 2);
}

TYPED_TEST(AccountStateTest, set_code_hash_changeset)
{
    auto db = test::make_db<TypeParam>();
    AccountState s{db};
    db.commit(StateChanges{
        .account_changes = {{b, Account{}}}, .storage_changes = {}});

    auto bs = typename decltype(s)::ChangeSet{s};

    bs.access_account(b);
    bs.create_account(a);
    bs.set_balance(a, 38'000);
    bs.set_nonce(a, 2);
    bs.set_code_hash(a, hash1);

    EXPECT_EQ(bs.get_code_hash(a), hash1);
    EXPECT_EQ(bs.get_code_hash(b), NULL_HASH);
}

TYPED_TEST(AccountStateTest, selfdestruct_changeset)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes =
            {{a, Account{.balance = 18'000}}, {c, Account{.balance = 38'000}}},
        .storage_changes = {}});

    AccountState s{db};
    s.merged_.emplace(b, diff_t{std::nullopt, Account{.balance = 28'000}});

    auto bs = typename decltype(s)::ChangeSet{s};

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

TYPED_TEST(AccountStateTest, destruct_touched_dead_changeset)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{.balance = 10'000}}, {b, Account{}}},
        .storage_changes = {}});

    AccountState s{db};

    auto bs = typename decltype(s)::ChangeSet{s};

    bs.create_account(a);
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

TYPED_TEST(AccountStateTest, revert_touched_changeset)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{.balance = 10'000, .nonce = 2}}},
        .storage_changes = {}});

    AccountState s{db};

    auto bs = typename decltype(s)::ChangeSet{s};

    bs.access_account(a);
    bs.set_balance(a, 15'000);
    bs.create_account(b);
    bs.revert();
    EXPECT_FALSE(s.account_exists(b));

    bs.access_account(a);
    EXPECT_EQ(bs.get_balance(a), bytes32_t{10'000});
    EXPECT_FALSE(bs.account_exists(b));
}

TYPED_TEST(AccountStateTest, can_merge_fresh)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes =
            {{b, Account{.balance = 40'000u}},
             {c, Account{.balance = 50'000u}}},
        .storage_changes = {}});

    AccountState t{db};

    auto s = typename decltype(t)::ChangeSet{t};

    s.access_account(b);
    s.access_account(c);
    s.create_account(a);
    s.set_nonce(a, 1);
    s.set_balance(a, 38'000);
    s.set_balance(b, 42'000);
    s.set_nonce(b, 3);
    (void)s.selfdestruct(c, b);
    s.destruct_suicides();

    EXPECT_TRUE(t.can_merge(s));
}

TYPED_TEST(AccountStateTest, can_merge_onto_merged)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes =
            {{b, Account{.balance = 40'000u}},
             {c, Account{.balance = 50'000u}}},
        .storage_changes = {}});

    AccountState t{db};
    t.merged_.emplace(a, diff_t{Account{.balance = 30'000}});
    t.merged_.emplace(b, diff_t{db.at(b), db.at(b)});
    t.merged_.emplace(c, diff_t{Account{.balance = 50'000}, std::nullopt});
    t.merged_[c].updated.reset();

    auto s = typename decltype(t)::ChangeSet{t};

    s.access_account(a);
    s.access_account(b);
    s.create_account(c);
    s.set_nonce(c, 1);
    s.set_balance(c, 38'000);
    s.set_balance(b, 42'000);
    s.set_nonce(b, 3);
    (void)s.selfdestruct(a, b);
    s.destruct_suicides();

    EXPECT_TRUE(t.can_merge(s));
}

TYPED_TEST(AccountStateTest, cant_merge_colliding_merge)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{.balance = 40'000u}}},
        .storage_changes = {}});

    AccountState t{db};
    diff_t r{db.at(a), db.at(a)};
    r.updated.value().balance = 80'000;

    auto s = typename decltype(t)::ChangeSet{t};

    s.access_account(a);
    s.set_balance(a, 80'000);

    t.merged_.emplace(a, r);

    EXPECT_FALSE(t.can_merge(s));
}

TYPED_TEST(AccountStateTest, cant_merge_deleted_merge)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{.balance = 40'000u}}},
        .storage_changes{}});

    AccountState t{db};
    diff_t r{db.at(a), db.at(a)};
    r.updated.value().balance = 60'000;

    auto s = typename decltype(t)::ChangeSet{t};

    s.access_account(a);
    s.set_balance(a, 80'000);

    t.merged_.emplace(a, r);
    t.merged_[a].updated.reset();

    EXPECT_FALSE(t.can_merge(s));
}

TYPED_TEST(AccountStateTest, cant_merge_conflicting_adds)
{
    auto db = test::make_db<TypeParam>();
    AccountState t{db};
    diff_t r{std::nullopt, Account{.balance = 10'000, .nonce = 1}};

    auto s = typename decltype(t)::ChangeSet{t};

    s.create_account(a);
    s.set_nonce(a, 1);
    s.set_balance(a, 80'000);

    t.merged_.emplace(a, r);

    EXPECT_FALSE(t.can_merge(s));
}

TYPED_TEST(AccountStateTest, cant_merge_conflicting_modifies)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{.balance = 40'000u}}},
        .storage_changes{}});

    AccountState t{db};
    diff_t r{db.at(a), db.at(a)};
    r.updated.value().balance = 80'000;

    auto s = typename decltype(t)::ChangeSet{t};

    s.access_account(a);
    s.set_balance(a, 60'000);

    t.merged_.emplace(a, r);

    EXPECT_FALSE(t.can_merge(s));
}

TYPED_TEST(AccountStateTest, cant_merge_conflicting_deleted)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes =
            {{b, Account{.balance = 10'000u, .nonce = 1}},
             {c, Account{.balance = 40'000u, .nonce = 2}}},
        .storage_changes = {}});

    AccountState t{db};
    diff_t r{db.at(c), db.at(c)};
    r.updated.reset();
    auto s = typename decltype(t)::ChangeSet{t};

    s.access_account(b);
    s.access_account(c);
    (void)s.selfdestruct(c, b);
    s.destruct_suicides();

    t.merged_.emplace(c, r);

    EXPECT_FALSE(t.can_merge(s));
}

TYPED_TEST(AccountStateTest, merge_multiple_changes)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes =
            {{b, Account{.balance = 40'000u}},
             {c, Account{.balance = 50'000u}}},
        .storage_changes = {}});

    AccountState t{db};

    {
        auto s = typename decltype(t)::ChangeSet{t};

        s.access_account(b);
        s.access_account(c);
        s.create_account(a);
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
        auto s = typename decltype(t)::ChangeSet{t};

        s.access_account(b);
        s.create_account(c);
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

TYPED_TEST(AccountStateTest, can_commit)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes =
            {{b, Account{.balance = 40'000u}},
             {c, Account{.balance = 50'000u}}},
        .storage_changes = {}});
    AccountState t{db};
    diff_t r{db.at(c), db.at(c)};
    r.updated.reset();

    t.merged_.emplace(a, Account{.balance = 30'000});
    t.merged_.emplace(b, diff_t{db.at(b), db.at(b)});
    t.merged_.emplace(c, r);

    EXPECT_TRUE(t.can_commit());
}

TYPED_TEST(AccountStateTest, cant_commit_merged_new_different_than_stored)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{.balance = 40'000u}}},
        .storage_changes = {}});
    AccountState t{db};
    t.merged_.emplace(a, diff_t{Account{.balance = 30'000}});

    EXPECT_FALSE(t.can_commit());
}

TYPED_TEST(AccountStateTest, cant_commit_merged_different_than_stored_balance)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{.balance = 40'000u}}},
        .storage_changes = {}});
    AccountState t{db};
    t.merged_.emplace(
        a, diff_t{Account{.balance = 30'000}, Account{.balance = 30'000}});

    EXPECT_FALSE(t.can_commit());
}

TYPED_TEST(AccountStateTest, cant_commit_merged_different_than_stored_nonce)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{.balance = 40'000u}}},
        .storage_changes = {}});
    AccountState t{db};
    t.merged_.emplace(
        a,
        diff_t{
            Account{.balance = 40'000, .nonce = 1},
            Account{.balance = 30'000}});

    EXPECT_FALSE(t.can_commit());
}

TYPED_TEST(AccountStateTest, cant_commit_merged_different_than_stored_code_hash)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{.code_hash = hash1}}},
        .storage_changes = {}});
    AccountState t{db};
    t.merged_.emplace(a, diff_t{Account{.code_hash = hash2}, Account{}});

    EXPECT_FALSE(t.can_commit());
}

TYPED_TEST(AccountStateTest, cant_commit_deleted_isnt_stored)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}}, .storage_changes = {}});
    AccountState t{db};
    diff_t r{Account{.balance = 10'000}, std::nullopt};
    r.updated.reset();

    t.merged_.emplace(b, r);
    EXPECT_FALSE(t.can_commit());
}

TYPED_TEST(AccountStateTest, can_commit_multiple)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes =
            {{b, Account{.balance = 40'000u}},
             {c, Account{.balance = 50'000u}},
             {d, Account{.balance = 60'000u}}},
        .storage_changes = {}});
    AccountState t{db};

    {
        auto s = typename decltype(t)::ChangeSet{t};

        s.access_account(b);
        s.access_account(c);
        s.create_account(a);
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
        auto s = typename decltype(t)::ChangeSet{t};

        s.access_account(a);
        s.access_account(b);
        s.access_account(d);
        s.create_account(c);
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
    StateChanges sc{.account_changes = t.gather_changes()};
    db.commit(sc);

    EXPECT_TRUE(db.contains(a));
    EXPECT_EQ(db.at(a).balance, 98'000);
    EXPECT_EQ(db.at(a).nonce, 1);
    EXPECT_EQ(db.at(b).balance, 48'000);
    EXPECT_EQ(db.at(b).nonce, 4);
    EXPECT_EQ(db.at(c).balance, 22'000);
    EXPECT_EQ(db.at(c).nonce, 1);
    EXPECT_FALSE(db.contains(d));
}
