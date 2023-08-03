#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>

#include <monad/state/value_state.hpp>

#include <monad/state/state_changes.hpp>

#include <monad/db/in_memory_db.hpp>
#include <monad/db/in_memory_trie_db.hpp>
#include <monad/db/rocks_db.hpp>
#include <monad/db/rocks_trie_db.hpp>

#include <monad/test/make_db.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::state;

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

using diff_t = InnerStorage::diff_t;

template <typename TDB>
struct ValueStateTest : public testing::Test
{
};
using DBTypes = ::testing::Types<
    db::InMemoryDB, db::RocksDB, db::InMemoryTrieDB, db::RocksTrieDB>;
TYPED_TEST_SUITE(ValueStateTest, DBTypes);

TYPED_TEST(ValueStateTest, access_storage)
{
    auto db = test::make_db<TypeParam>();
    ValueState t{db};

    auto s = typename decltype(t)::ChangeSet{t};

    EXPECT_EQ(s.access_storage(a, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(a, key1), EVMC_ACCESS_WARM);
    EXPECT_EQ(s.access_storage(b, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(b, key1), EVMC_ACCESS_WARM);
    EXPECT_EQ(s.access_storage(a, key2), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(a, key2), EVMC_ACCESS_WARM);
    EXPECT_EQ(s.access_storage(b, key2), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(b, key2), EVMC_ACCESS_WARM);
}

TYPED_TEST(ValueStateTest, copy)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}, {c, Account{}}},
        .storage_changes = {
            {a, {{key1, value1}, {key2, value2}}},
            {c, {{key1, value1}, {key2, value2}}}}});
    ValueState s{db};

    auto t = typename decltype(s)::ChangeSet{s};
    auto r = typename decltype(s)::ChangeSet{s};

    EXPECT_EQ(r.access_storage(a, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(r.access_storage(b, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(r.set_storage(a, key1, value1), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(r.set_storage(c, key1, null), EVMC_STORAGE_DELETED);

    EXPECT_EQ(t.access_storage(a, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(t.access_storage(b, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(t.set_storage(a, key1, value1), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(t.set_storage(b, key1, value2), EVMC_STORAGE_ADDED);
}

TYPED_TEST(ValueStateTest, get_storage)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}, {b, Account{}}},
        .storage_changes = {
            {a, {{key1, value1}, {key2, value2}}}, {b, {{key1, value1}}}}});

    ValueState t{db};
    t.merged_.storage_[a].emplace(key2, diff_t{value2, value3});
    t.merged_.storage_[b][key1] = bytes32_t{};

    auto s = typename decltype(t)::ChangeSet{t};

    EXPECT_EQ(s.get_storage(a, key1), value1);
    EXPECT_EQ(s.get_storage(a, key2), value3);
    EXPECT_EQ(s.get_storage(a, key3), null);
    EXPECT_EQ(s.get_storage(b, key1), null);
}

TYPED_TEST(ValueStateTest, set_add_delete_touched)
{
    auto db = test::make_db<TypeParam>();
    ValueState t{db};

    auto s = typename decltype(t)::ChangeSet{t};

    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_ADDED);
    EXPECT_EQ(s.get_storage(a, key1), value1);
    EXPECT_EQ(s.set_storage(a, key1, null), EVMC_STORAGE_ADDED_DELETED);
    EXPECT_EQ(s.get_storage(a, key1), null);
    EXPECT_EQ(s.set_storage(a, key1, value2), EVMC_STORAGE_ADDED);
}

TYPED_TEST(ValueStateTest, set_modify_delete_storage)
{
    auto db = test::make_db<TypeParam>();
    ValueState t{db};
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}},
        .storage_changes = {{a, {{key1, value1}, {key2, value2}}}}});

    auto s = typename decltype(t)::ChangeSet{t};

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

TYPED_TEST(ValueStateTest, set_modify_delete_merged)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}},
        .storage_changes = {{a, {{key1, value1}, {key2, value2}}}}});

    ValueState t{db};
    t.merged_.storage_[a].emplace(key1, diff_t{value1, value2});
    t.merged_.storage_[a].emplace(key2, diff_t{value2, value1});

    auto s = typename decltype(t)::ChangeSet{t};

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

TYPED_TEST(ValueStateTest, multiple_get_and_set_from_storage)
{
    auto db = test::make_db<TypeParam>();
    ValueState t{db};
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}, {b, Account{}}, {c, Account{}}},
        .storage_changes = {
            {a, {{key1, value1}, {key2, value2}}},
            {b, {{key1, value1}, {key2, value2}}},
            {c, {{key1, value1}, {key2, value2}}}}});

    auto s = typename decltype(t)::ChangeSet{t};

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

TYPED_TEST(ValueStateTest, multiple_get_and_set_from_merged)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}, {c, Account{}}},
        .storage_changes = {
            {a, {{key1, value1}, {key2, value2}}},
            {c, {{key1, value1}, {key2, value2}}}}});

    ValueState t{db};
    t.merged_.storage_[a].emplace(key1, diff_t{value1, value2});
    t.merged_.storage_[c].emplace(key1, diff_t{value1, value2});

    auto s = typename decltype(t)::ChangeSet{t};

    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_MODIFIED);
    EXPECT_EQ(s.set_storage(a, key1, null), EVMC_STORAGE_MODIFIED_DELETED);
    EXPECT_EQ(s.set_storage(a, key1, value2), EVMC_STORAGE_DELETED_RESTORED);
    EXPECT_EQ(s.set_storage(a, key1, value2), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_MODIFIED);

    EXPECT_EQ(s.set_storage(a, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(s.set_storage(a, key2, value1), EVMC_STORAGE_DELETED_ADDED);
    EXPECT_EQ(s.set_storage(a, key2, value1), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(s.set_storage(a, key2, value3), EVMC_STORAGE_ASSIGNED);

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

TYPED_TEST(ValueStateTest, revert)
{
    auto db = test::make_db<TypeParam>();
    ValueState t{db};

    auto s = typename decltype(t)::ChangeSet{t};

    EXPECT_EQ(s.access_storage(a, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(b, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_ADDED);
    EXPECT_EQ(s.set_storage(c, key1, value1), EVMC_STORAGE_ADDED);

    s.revert();

    EXPECT_EQ(s.access_storage(a, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(b, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.get_storage(a, key1), null);
    EXPECT_EQ(s.get_storage(c, key1), null);
    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_ADDED);
    EXPECT_EQ(s.set_storage(c, key1, value1), EVMC_STORAGE_ADDED);
}

TYPED_TEST(ValueStateTest, can_merge)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}, {b, Account{}}},
        .storage_changes = {
            {a, {{key1, value1}, {key2, value2}}},
            {b, {{key1, value1}, {key2, value2}}}}});
    ValueState s{db};

    auto t = typename decltype(s)::ChangeSet{s};

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

TYPED_TEST(ValueStateTest, can_merge_added)
{
    auto db = test::make_db<TypeParam>();
    ValueState s{db};

    auto t = typename decltype(s)::ChangeSet{s};

    EXPECT_EQ(t.set_storage(c, key2, value1), EVMC_STORAGE_ADDED);
    EXPECT_TRUE(s.can_merge(t));
}

TYPED_TEST(ValueStateTest, can_merge_deleted)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}},
        .storage_changes = {{a, {{key2, value2}}}}});
    ValueState s{db};

    auto t = typename decltype(s)::ChangeSet{s};

    EXPECT_EQ(t.set_storage(a, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_TRUE(s.can_merge(t));
}

TYPED_TEST(ValueStateTest, can_merge_modified)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}},
        .storage_changes = {{a, {{key1, value1}}}}});
    ValueState s{db};

    auto t = typename decltype(s)::ChangeSet{s};

    EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);
    EXPECT_TRUE(s.can_merge(t));
}

TYPED_TEST(ValueStateTest, can_merge_modify_merged_added)
{
    auto db = test::make_db<TypeParam>();
    ValueState s{db};

    {
        auto t = typename decltype(s)::ChangeSet{s};

        EXPECT_EQ(t.set_storage(c, key2, value1), EVMC_STORAGE_ADDED);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
    }
    {
        auto t = typename decltype(s)::ChangeSet{s};
        EXPECT_EQ(t.set_storage(c, key2, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
    }
}

TYPED_TEST(ValueStateTest, can_merge_delete_merged_added)
{
    auto db = test::make_db<TypeParam>();
    ValueState s{db};

    {
        auto t = typename decltype(s)::ChangeSet{s};
        EXPECT_EQ(t.set_storage(c, key2, value1), EVMC_STORAGE_ADDED);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
    }
    {
        auto t = typename decltype(s)::ChangeSet{s};
        EXPECT_EQ(t.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
    }
}

TYPED_TEST(ValueStateTest, can_merge_add_on_merged_deleted)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}},
        .storage_changes = {{a, {{key2, value2}}}}});
    ValueState s{db};

    {
        auto t = typename decltype(s)::ChangeSet{s};
        EXPECT_EQ(t.set_storage(a, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
    }
    {
        auto t = typename decltype(s)::ChangeSet{s};
        EXPECT_EQ(t.set_storage(a, key2, value1), EVMC_STORAGE_ADDED);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
    }
}

TYPED_TEST(ValueStateTest, can_merge_delete_merged_modified)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}},
        .storage_changes = {{a, {{key1, value1}}}}});
    ValueState s{db};

    {
        auto t = typename decltype(s)::ChangeSet{s};
        EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
    }
    {
        auto t = typename decltype(s)::ChangeSet{s};
        EXPECT_EQ(t.set_storage(a, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
        {
            auto r = typename decltype(s)::ChangeSet{s};
            EXPECT_EQ(r.get_storage(a, key1), null);
        }
    }
}

TYPED_TEST(ValueStateTest, cant_merge_colliding_merge)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}},
        .storage_changes = {{a, {{key1, value1}}}}});
    ValueState s{db};

    auto t = typename decltype(s)::ChangeSet{s};

    EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);

    s.merged_.storage_[a].emplace(key1, diff_t{value1, value2});

    EXPECT_FALSE(s.can_merge(t));
}

TYPED_TEST(ValueStateTest, cant_merge_deleted_merge)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}},
        .storage_changes = {{a, {{key1, value1}}}}});
    ValueState s{db};

    auto t = typename decltype(s)::ChangeSet{s};

    EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);

    s.merged_.storage_[a][key1] = bytes32_t{};

    EXPECT_FALSE(s.can_merge(t));
}

TYPED_TEST(ValueStateTest, cant_merge_conflicting_adds)
{
    auto db = test::make_db<TypeParam>();
    ValueState s{db};

    auto t = typename decltype(s)::ChangeSet{s};

    EXPECT_EQ(t.set_storage(a, key1, value1), EVMC_STORAGE_ADDED);

    s.merged_.storage_[a].emplace(key1, diff_t{{}, value2});

    EXPECT_FALSE(s.can_merge(t));
}

TYPED_TEST(ValueStateTest, cant_merge_conflicting_modifies)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}},
        .storage_changes = {{a, {{key1, value3}}}}});
    ValueState s{db};

    auto t = typename decltype(s)::ChangeSet{s};

    EXPECT_EQ(t.set_storage(a, key1, value1), EVMC_STORAGE_MODIFIED);

    s.merged_.storage_[a].emplace(key1, diff_t{value3, value2});

    EXPECT_FALSE(s.can_merge(t));
}

TYPED_TEST(ValueStateTest, cant_merge_conflicting_deleted)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}},
        .storage_changes = {{a, {{key1, value1}}}}});
    ValueState s{db};

    auto t = typename decltype(s)::ChangeSet{s};

    EXPECT_EQ(t.set_storage(a, key1, null), EVMC_STORAGE_DELETED);

    s.merged_.storage_[a][key1] = bytes32_t{};

    EXPECT_FALSE(s.can_merge(t));
}

TYPED_TEST(ValueStateTest, cant_merge_delete_conflicts_with_modify)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}},
        .storage_changes = {{a, {{key1, value1}}}}});
    ValueState s{db};

    auto t = typename decltype(s)::ChangeSet{s};

    EXPECT_EQ(t.set_storage(a, key1, null), EVMC_STORAGE_DELETED);

    s.merged_.storage_[a].emplace(key1, diff_t{value1, value2});

    EXPECT_FALSE(s.can_merge(t));
}

TYPED_TEST(ValueStateTest, merge_touched_multiple)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}, {b, Account{}}},
        .storage_changes = {{a, {{key1, value1}}}, {b, {{key1, value1}}}}});
    ValueState s{db};

    {
        auto t = typename decltype(s)::ChangeSet{s};

        EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(t.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(t.set_storage(c, key1, value1), EVMC_STORAGE_ADDED);

        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
    }

    {
        auto u = typename decltype(s)::ChangeSet{s};

        EXPECT_EQ(u.set_storage(a, key1, value3), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(u.set_storage(b, key1, value1), EVMC_STORAGE_ADDED);
        EXPECT_EQ(u.set_storage(c, key1, null), EVMC_STORAGE_DELETED);

        EXPECT_TRUE(s.can_merge(u));
        s.merge_touched(u);
    }
}

TYPED_TEST(ValueStateTest, can_commit)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}, {b, Account{}}},
        .storage_changes = {{a, {{key1, value1}}}, {b, {{key1, value1}}}}});
    ValueState s{db};

    {
        auto t = typename decltype(s)::ChangeSet{s};

        EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(t.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(t.set_storage(c, key1, value1), EVMC_STORAGE_ADDED);

        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
        EXPECT_TRUE(s.can_commit());
    }

    {
        auto u = typename decltype(s)::ChangeSet{s};

        EXPECT_EQ(u.set_storage(a, key1, value3), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(u.set_storage(b, key1, value1), EVMC_STORAGE_ADDED);
        EXPECT_EQ(u.set_storage(c, key1, null), EVMC_STORAGE_DELETED);

        EXPECT_TRUE(s.can_merge(u));
        s.merge_touched(u);
        EXPECT_TRUE(s.can_commit());
    }
}

TYPED_TEST(ValueStateTest, can_commit_restored)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}, {b, Account{}}},
        .storage_changes = {{a, {{key1, value1}}}, {b, {{key1, value1}}}}});
    ValueState s{db};

    {
        auto t = typename decltype(s)::ChangeSet{s};
        EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(
            t.set_storage(a, key1, value1), EVMC_STORAGE_MODIFIED_RESTORED);
        EXPECT_EQ(t.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(
            t.set_storage(b, key1, value1), EVMC_STORAGE_DELETED_RESTORED);
        EXPECT_EQ(t.set_storage(c, key1, value1), EVMC_STORAGE_ADDED);
        EXPECT_EQ(t.set_storage(c, key1, null), EVMC_STORAGE_ADDED_DELETED);

        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
        EXPECT_TRUE(s.can_commit());
    }

    {
        auto u = typename decltype(s)::ChangeSet{s};
        EXPECT_EQ(u.set_storage(a, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(
            u.set_storage(a, key1, value1), EVMC_STORAGE_DELETED_RESTORED);
        EXPECT_EQ(u.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(
            u.set_storage(b, key1, value1), EVMC_STORAGE_MODIFIED_RESTORED);
        EXPECT_EQ(u.set_storage(c, key1, value1), EVMC_STORAGE_ADDED);
        EXPECT_EQ(u.set_storage(c, key1, null), EVMC_STORAGE_ADDED_DELETED);

        EXPECT_TRUE(s.can_merge(u));
        s.merge_touched(u);
        EXPECT_TRUE(s.can_commit());
    }
}

TYPED_TEST(ValueStateTest, commit_all_merged)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}, {b, Account{}}},
        .storage_changes = {{a, {{key1, value1}}}, {b, {{key1, value1}}}}});
    ValueState s{db};

    {
        auto t = typename decltype(s)::ChangeSet{s};
        EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(
            t.set_storage(a, key1, value1), EVMC_STORAGE_MODIFIED_RESTORED);
        EXPECT_EQ(t.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(
            t.set_storage(b, key1, value1), EVMC_STORAGE_DELETED_RESTORED);
        EXPECT_EQ(t.set_storage(c, key1, value1), EVMC_STORAGE_ADDED);
        EXPECT_EQ(t.set_storage(c, key1, null), EVMC_STORAGE_ADDED_DELETED);

        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
        EXPECT_TRUE(s.can_commit());
    }

    {
        auto u = typename decltype(s)::ChangeSet{s};
        EXPECT_EQ(u.set_storage(a, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(
            u.set_storage(a, key1, value1), EVMC_STORAGE_DELETED_RESTORED);
        EXPECT_EQ(u.set_storage(b, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(
            u.set_storage(b, key1, value1), EVMC_STORAGE_MODIFIED_RESTORED);
        EXPECT_EQ(u.set_storage(c, key1, value1), EVMC_STORAGE_ADDED);
        EXPECT_EQ(u.set_storage(c, key1, null), EVMC_STORAGE_ADDED_DELETED);

        EXPECT_TRUE(s.can_merge(u));
        s.merge_touched(u);
        EXPECT_TRUE(s.can_commit());
    }

    auto _ = s.gather_changes();
}

TYPED_TEST(ValueStateTest, get_after_set)
{
    auto db = test::make_db<TypeParam>();
    db.commit(StateChanges{
        .account_changes = {{a, Account{}}},
        .storage_changes = {{a, {{key1, value1}}}}});
    ValueState s{db};

    auto t = typename decltype(s)::ChangeSet{s};
    EXPECT_EQ(t.set_storage(a, key1, value1), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(t.set_storage(a, key1, null), EVMC_STORAGE_DELETED);
    EXPECT_EQ(t.get_storage(a, key1), null);
}
