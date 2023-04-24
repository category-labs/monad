#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>

#include <monad/db/account_state.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::db;

static constexpr auto a = 0x5353535353535353535353535353535353535353_address;
static constexpr auto b = 0xbebebebebebebebebebebebebebebebebebebebe_address;
static constexpr auto c = 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5_address;

using store_t = std::unordered_map<address_t, Account>;

TEST(Accounts, access_account)
{
    store_t db{};
    Accounts s{db};
    db.insert({a, {}});
    db.insert({b, {}});

    EXPECT_EQ(s.access_account(a), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_account(a), EVMC_ACCESS_WARM);
    EXPECT_EQ(s.access_account(b), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_account(b), EVMC_ACCESS_WARM);
}

TEST(Accounts, create_account)
{
    store_t db{};
    Accounts s{db};

    s.create_contract(a);
    s.set_nonce(a, 1);
    s.set_balance(a, 38'000);

    EXPECT_EQ(s.accounts_.size(), 0u);
    EXPECT_EQ(s.touched_accounts_.size(), 1u);
    EXPECT_EQ(s.created_accounts_.size(), 1u);

    s.commit();

    EXPECT_EQ(s.accounts_.size(), 1u);
    EXPECT_EQ(s.touched_accounts_.size(), 0u);
    EXPECT_EQ(s.created_accounts_.size(), 0u);
    EXPECT_EQ(s.accounts_.at(a).balance, 38'000);

    s.access_account(a);
    s.set_balance(a, 15'000);
    s.commit();

    EXPECT_EQ(s.accounts_.at(a).balance, 15'000);
}

TEST(Accounts, account_exists)
{
    store_t db{};
    Accounts s{db};
    db.insert({a, {}});

    s.create_contract(b);

    EXPECT_TRUE(s.account_exists(a));
    EXPECT_TRUE(s.account_exists(b));
    EXPECT_FALSE(s.account_exists(c));
}

TEST(Accounts, destruct_account)
{
    store_t db{};
    Accounts s{db};

    s.create_contract(a);
    s.create_contract(b);
    s.set_nonce(a, 1);
    s.set_balance(a, 38'000);
    s.set_nonce(b, 1);
    s.set_balance(b, 28'000);
    s.commit();

    s.access_account(a);
    s.access_account(b);
    s.selfdestruct(a, b);
    EXPECT_EQ(s.total_selfdestructs(), 1u);
    s.destruct_suicides();
    s.commit();

    EXPECT_EQ(s.accounts_.size(), 1u);
    EXPECT_EQ(s.accounts_.at(b).balance, 66'000);
}

TEST(Accounts, destruct_touched_dead)
{
    store_t db{};
    Accounts s{db};

    s.create_contract(a);
    s.set_balance(a, 38'000);
    s.destruct_touched_dead();
    s.commit();
    EXPECT_EQ(s.accounts_.size(), 1u);

    s.access_account(a);
    s.set_balance(a, 0);
    s.destruct_touched_dead();
    s.commit();

    EXPECT_EQ(s.accounts_.size(), 0u);
}

TEST(Accounts, revert_touched)
{
    store_t db{};
    Accounts s{db};

    s.create_contract(a);
    s.set_nonce(a, 1);
    s.set_balance(a, 38'000);
    s.commit();

    s.access_account(a);
    s.set_balance(a, 15'000);
    s.create_contract(b);
    s.revert();
    s.destruct_suicides();

    EXPECT_EQ(s.accounts_.size(), 1u);
    EXPECT_EQ(s.accounts_.at(a).balance, 38'000);
    EXPECT_EQ(s.created_accounts_.size(), 0u);
}


TEST(AccountState, get_copy)
{}

TEST(AccountState, can_merge)
{}

TEST(AccountState, cant_merge_new_merge)
{}

TEST(AccountState, cant_merge_deleted_merge)
{}

TEST(AccountState, cant_merge_conflicting_adds)
{}

TEST(AccountState, cant_merge_conflicting_modifies)
{}

TEST(AccountState, cant_merge_conflicting_deleted)
{}

TEST(AccountState, merge_touched)
{}

TEST(AccountState, can_commit)
{}

TEST(AccountState, can_commit_restored)
{}

TEST(AccountState, commit_all_merged)
{}

