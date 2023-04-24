#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>

#include <monad/db/account_storage.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::db;

static constexpr auto a = 0xbebebebebebebebebebebebebebebebebebebebe_address;
static constexpr auto b = 0xEA674fdDe714fd979de3EdF0F56AA9716B898ec8_address;
static constexpr auto c = 0x61C808D82A3Ac53231750daDc13c777b59310bD9_address;
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

using account_storage_t = std::unordered_map<bytes32_t, bytes32_t>;
using store_t = std::unordered_map<address_t, account_storage_t>;

TEST(AccountStorage, access_storage)
{
    store_t db{};
    AccountStorage s{db};
    EXPECT_EQ(s.access_storage(a, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(a, key1), EVMC_ACCESS_WARM);
    EXPECT_EQ(s.access_storage(b, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(b, key1), EVMC_ACCESS_WARM);
    EXPECT_EQ(s.access_storage(a, key2), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(a, key2), EVMC_ACCESS_WARM);
    EXPECT_EQ(s.access_storage(b, key2), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(b, key2), EVMC_ACCESS_WARM);
}

TEST(AccountStorage, get_storage)
{
    store_t db{};
    db[a].insert({key1, value1});
    db[a].insert({key2, value2});
    db[b].insert({key1, value1});

    AccountStorage s{db};
    s.merged_.storage_[a].insert({key2, {value2, value3}});
    s.merged_.deleted_storage_[b].insert({value1, key1});

    EXPECT_EQ(s.get_storage(a, key1), value1);
    EXPECT_EQ(s.get_storage(a, key2), value3);
    EXPECT_EQ(s.get_storage(a, key3), null);
    EXPECT_EQ(s.get_storage(b, key1), null);
}

TEST(AccountStorage, set_add_delete_touched)
{
    store_t db{};
    AccountStorage s{db};

    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_ADDED);
    EXPECT_EQ(s.get_storage(a, key1), value1);
    EXPECT_EQ(s.set_storage(a, key1, null), EVMC_STORAGE_ADDED_DELETED);
    EXPECT_EQ(s.get_storage(a, key1), null);
    EXPECT_EQ(s.set_storage(a, key1, value2), EVMC_STORAGE_ADDED);
}

TEST(AccountStorage, set_modify_delete_storage)
{
    store_t db{};
    AccountStorage s{db};
    db[a].insert({key1, value1});
    db[a].insert({key2, value2});

    EXPECT_EQ(s.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.set_storage(a, key1, null), EVMC_STORAGE_MODIFIED_DELETED);
    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_DELETED_RESTORED);
    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_MODIFIED_RESTORED);

    EXPECT_EQ(s.set_storage(a, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(s.set_storage(a, key2, value1), EVMC_STORAGE_DELETED_ADDED);

    EXPECT_EQ(s.get_storage(a, key1), value1);
    EXPECT_EQ(s.get_storage(a, key2), value1);
}

TEST(AccountStorage, set_modify_delete_merged)
{
    store_t db{};
    db[a].insert({key1, value1});
    db[a].insert({key2, value2});

    AccountStorage s{db};
    s.merged_.storage_[a].insert({key1, {value1, value2}});
    s.merged_.storage_[a].insert({key2, {value2, value1}});

    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.set_storage(a, key1, null), EVMC_STORAGE_MODIFIED_DELETED);
    EXPECT_EQ(s.set_storage(a, key1, value2), EVMC_STORAGE_DELETED_RESTORED);
    EXPECT_EQ(s.set_storage(a, key1, value2), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED_RESTORED);

    EXPECT_EQ(s.set_storage(a, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(s.set_storage(a, key2, value2), EVMC_STORAGE_DELETED_ADDED);

    EXPECT_EQ(s.get_storage(a, key1), value2);
    EXPECT_EQ(s.get_storage(a, key2), value2);
}

TEST(AccountStorage, multiple_get_and_set_from_storage)
{
    store_t db{};
    AccountStorage s{db};
    db[a].insert({key1, value1});
    db[a].insert({key2, value2});
    db[b].insert({key1, value1});
    db[b].insert({key2, value2});
    db[c].insert({key1, value1});
    db[c].insert({key2, value2});

    EXPECT_EQ(s.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.set_storage(a, key1, null), EVMC_STORAGE_MODIFIED_DELETED);
    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_DELETED_RESTORED);
    EXPECT_EQ(s.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);

    EXPECT_EQ(s.set_storage(a, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(s.set_storage(a, key2, value2), EVMC_STORAGE_DELETED_RESTORED);
    EXPECT_EQ(s.set_storage(a, key2, value1), EVMC_STORAGE_MODIFIED);

    EXPECT_EQ(s.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.set_storage(b, key1, null), EVMC_STORAGE_MODIFIED_DELETED);
    EXPECT_EQ(s.set_storage(b, key1, value2), EVMC_STORAGE_DELETED_ADDED);

    EXPECT_EQ(s.set_storage(b, key2, value2), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.set_storage(b, key2, value1), EVMC_STORAGE_MODIFIED);

    EXPECT_EQ(s.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(s.set_storage(c, key2, null), EVMC_STORAGE_DELETED);

    EXPECT_EQ(s.get_storage(a, key1), value2);
    EXPECT_EQ(s.get_storage(a, key2), value1);
    EXPECT_EQ(s.get_storage(b, key1), value2);
    EXPECT_EQ(s.get_storage(b, key2), value1);
    EXPECT_EQ(s.get_storage(c, key1), null);
    EXPECT_EQ(s.get_storage(c, key2), null);
}

TEST(AccountStorage, multiple_get_and_set_from_merged)
{
    store_t db{};
    db[a].insert({key1, value1});
    db[a].insert({key2, value2});
    db[c].insert({key1, value1});
    db[c].insert({key2, value2});

    AccountStorage s{db};
    s.merged_.storage_[a].insert({key1, {value1, value2}});
    s.merged_.storage_[c].insert({key1, {value1, value2}});

    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.set_storage(a, key1, null), EVMC_STORAGE_MODIFIED_DELETED);
    EXPECT_EQ(s.set_storage(a, key1, value2), EVMC_STORAGE_DELETED_RESTORED);
    EXPECT_EQ(s.set_storage(a, key1, value2), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_MODIFIED);

    EXPECT_EQ(s.set_storage(a, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(s.set_storage(a, key2, value1), EVMC_STORAGE_DELETED_ADDED);
    EXPECT_EQ(s.set_storage(a, key2, value1), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.set_storage(a, key2, value3), EVMC_STORAGE_MODIFIED);

    EXPECT_EQ(s.set_storage(b, key1, value1), EVMC_STORAGE_ADDED);
    EXPECT_EQ(s.set_storage(b, key1, value2), EVMC_STORAGE_ASSIGNED);

    EXPECT_EQ(s.set_storage(b, key2, value2), EVMC_STORAGE_ADDED);
    EXPECT_EQ(s.set_storage(b, key2, null), EVMC_STORAGE_ADDED_DELETED);

    EXPECT_EQ(s.set_storage(c, key1, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(s.set_storage(c, key2, null), EVMC_STORAGE_DELETED);

    EXPECT_EQ(s.get_storage(a, key1), value1);
    EXPECT_EQ(s.get_storage(a, key2), value3);
    EXPECT_EQ(s.get_storage(b, key1), value2);
    EXPECT_EQ(s.get_storage(b, key2), null);
    EXPECT_EQ(s.get_storage(c, key1), null);
    EXPECT_EQ(s.get_storage(c, key2), null);
}

TEST(AccountStorage, revert_touched)
{
    store_t db{};
    AccountStorage s{db};

    EXPECT_EQ(s.access_storage(a, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(b, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_ADDED);
    EXPECT_EQ(s.set_storage(c, key1, value1), EVMC_STORAGE_ADDED);

    s.revert_touched();

    EXPECT_EQ(s.access_storage(a, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(b, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.get_storage(a, key1), null);
    EXPECT_EQ(s.get_storage(c, key1), null);
    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_ADDED);
    EXPECT_EQ(s.set_storage(c, key1, value1), EVMC_STORAGE_ADDED);
}

TEST(AccountStorage, get_copy)
{
    store_t db{};
    db[a].insert({key1, value1});
    db[a].insert({key2, value2});
    db[c].insert({key1, value1});
    db[c].insert({key2, value2});
    AccountStorage s{db};

    auto t = s.get_copy();

    EXPECT_EQ(s.access_storage(a, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(b, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.set_storage(c, key1, null), EVMC_STORAGE_DELETED);

    EXPECT_EQ(t.access_storage(a, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(t.access_storage(b, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(t.set_storage(a, key1, value1), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(t.set_storage(b, key1, value2), EVMC_STORAGE_ADDED);
}

TEST(AccountStorage, can_merge)
{
    store_t db{};
    db[a].insert({key1, value1});
    db[a].insert({key2, value2});
    db[b].insert({key1, value1});
    db[b].insert({key2, value2});
    AccountStorage s{db};

    auto t = s.get_copy();

    EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(t.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(t.set_storage(c, key1, value1), EVMC_STORAGE_ADDED);

    EXPECT_EQ(t.set_storage(a, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(t.set_storage(a, key2, value2), EVMC_STORAGE_DELETED_RESTORED);
    EXPECT_EQ(t.set_storage(b, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(t.set_storage(b, key2, value1), EVMC_STORAGE_DELETED_ADDED);
    EXPECT_EQ(t.set_storage(c, key2, value1), EVMC_STORAGE_ADDED);

    EXPECT_TRUE(s.can_merge(t));
}

TEST(AccountStorage, cant_merge_new_merge)
{
    store_t db{};
    db[a].insert({key1, value1});
    AccountStorage s{db};

    auto t = s.get_copy();

    EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);

    s.merged_.storage_[a].insert({key1, {value1, value2}});

    EXPECT_FALSE(s.can_merge(t));
}

TEST(AccountStorage, cant_merge_deleted_merge)
{
    store_t db{};
    db[a].insert({key1, value1});
    AccountStorage s{db};

    auto t = s.get_copy();

    EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);

    s.merged_.deleted_storage_[a].insert(deleted_key{value1, key1});

    EXPECT_FALSE(s.can_merge(t));
}

TEST(AccountStorage, cant_merge_conflicting_adds)
{
    store_t db{};
    AccountStorage s{db};

    auto t = s.get_copy();

    EXPECT_EQ(t.set_storage(a, key1, value1), EVMC_STORAGE_ADDED);

    s.merged_.storage_[a].insert({key1, {{}, value2}});

    EXPECT_FALSE(s.can_merge(t));
}

TEST(AccountStorage, cant_merge_conflicting_modifies)
{
    store_t db{};
    db[a].insert({key1, value3});
    AccountStorage s{db};

    auto t = s.get_copy();

    EXPECT_EQ(t.set_storage(a, key1, value1), EVMC_STORAGE_MODIFIED);

    s.merged_.storage_[a].insert({key1, {value3, value2}});

    EXPECT_FALSE(s.can_merge(t));
}

TEST(AccountStorage, cant_merge_conflicting_deleted)
{
    store_t db{};
    db[a].insert({key1, value1});
    AccountStorage s{db};

    auto t = s.get_copy();

    EXPECT_EQ(t.set_storage(a, key1, null), EVMC_STORAGE_DELETED);

    s.merged_.deleted_storage_[a].insert({value1, key1});

    EXPECT_FALSE(s.can_merge(t));
}

TEST(AccountStorage, merge_touched)
{
    store_t db{};
    db[a].insert({key1, value1});
    db[b].insert({key1, value1});
    AccountStorage s{db};

    {
        auto t = s.get_copy();

        EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(t.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(t.set_storage(c, key1, value1), EVMC_STORAGE_ADDED);

        EXPECT_TRUE(s.merge_touched(t));
    }

    {
        auto u = s.get_copy();

        EXPECT_EQ(u.set_storage(a, key1, value3), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(u.set_storage(b, key1, value1), EVMC_STORAGE_ADDED);
        EXPECT_EQ(u.set_storage(c, key1, null), EVMC_STORAGE_DELETED);

        EXPECT_TRUE(s.merge_touched(u));
    }
}

TEST(AccountStorage, can_commit)
{
    store_t db{};
    db[a].insert({key1, value1});
    db[b].insert({key1, value1});
    AccountStorage s{db};

    {
        auto t = s.get_copy();

        EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(t.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(t.set_storage(c, key1, value1), EVMC_STORAGE_ADDED);

        EXPECT_TRUE(s.merge_touched(t));
        EXPECT_TRUE(s.can_commit());
    }

    {
        auto u = s.get_copy();

        EXPECT_EQ(u.set_storage(a, key1, value3), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(u.set_storage(b, key1, value1), EVMC_STORAGE_ADDED);
        EXPECT_EQ(u.set_storage(c, key1, null), EVMC_STORAGE_DELETED);

        EXPECT_TRUE(s.merge_touched(u));
        EXPECT_TRUE(s.can_commit());
    }
}

TEST(AccountStorage, can_commit_restored)
{
    store_t db{};
    db[a].insert({key1, value1});
    db[b].insert({key1, value1});
    AccountStorage s{db};

    {
        auto t = s.get_copy();

        EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(t.set_storage(a, key1, value1), EVMC_STORAGE_MODIFIED_RESTORED);
        EXPECT_EQ(t.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(t.set_storage(b, key1, value1), EVMC_STORAGE_DELETED_RESTORED);
        EXPECT_EQ(t.set_storage(c, key1, value1), EVMC_STORAGE_ADDED);
        EXPECT_EQ(t.set_storage(c, key1, null), EVMC_STORAGE_ADDED_DELETED);

        EXPECT_TRUE(s.merge_touched(t));
        EXPECT_TRUE(s.can_commit());
    }

    {
        auto u = s.get_copy();
        EXPECT_EQ(u.set_storage(a, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(u.set_storage(a, key1, value1), EVMC_STORAGE_DELETED_RESTORED);
        EXPECT_EQ(u.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(u.set_storage(b, key1, value1), EVMC_STORAGE_MODIFIED_RESTORED);
        EXPECT_EQ(u.set_storage(c, key1, value1), EVMC_STORAGE_ADDED);
        EXPECT_EQ(u.set_storage(c, key1, null), EVMC_STORAGE_ADDED_DELETED);

        EXPECT_TRUE(s.merge_touched(u));
        EXPECT_TRUE(s.can_commit());
    }
}

TEST(AccountStorage, commit_all_merged)
{
    store_t db{};
    db[a].insert({key1, value1});
    db[b].insert({key1, value1});
    AccountStorage s{db};

    {
        auto t = s.get_copy();

        EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(t.set_storage(a, key1, value1), EVMC_STORAGE_MODIFIED_RESTORED);
        EXPECT_EQ(t.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(t.set_storage(b, key1, value1), EVMC_STORAGE_DELETED_RESTORED);
        EXPECT_EQ(t.set_storage(c, key1, value1), EVMC_STORAGE_ADDED);
        EXPECT_EQ(t.set_storage(c, key1, null), EVMC_STORAGE_ADDED_DELETED);

        EXPECT_TRUE(s.merge_touched(t));
        EXPECT_TRUE(s.can_commit());
    }

    {
        auto u = s.get_copy();
        EXPECT_EQ(u.set_storage(a, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(u.set_storage(a, key1, value1), EVMC_STORAGE_DELETED_RESTORED);
        EXPECT_EQ(u.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(u.set_storage(b, key1, value1), EVMC_STORAGE_MODIFIED_RESTORED);
        EXPECT_EQ(u.set_storage(c, key1, value1), EVMC_STORAGE_ADDED);
        EXPECT_EQ(u.set_storage(c, key1, null), EVMC_STORAGE_ADDED_DELETED);

        EXPECT_TRUE(s.merge_touched(u));
        EXPECT_TRUE(s.can_commit());
    }

    s.commit_all_merged();
}
