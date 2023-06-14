#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>
#include <monad/db/trie_db.hpp>

#include <monad/db/value_store.hpp>

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

template <typename TDB>
struct ValueStoreTest : public testing::Test
{
};
using DBTypes =
    ::testing::Types<InMemoryDB, InMemoryTrieDB, RocksTrieDB>;
TYPED_TEST_SUITE(ValueStoreTest, DBTypes);

TYPED_TEST(ValueStoreTest, access_storage)
{
    TypeParam db{};
    ValueStore t{db};

    auto s = typename decltype(t)::WorkingCopy{t};

    EXPECT_EQ(s.access_storage(a, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(a, key1), EVMC_ACCESS_WARM);
    EXPECT_EQ(s.access_storage(b, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(b, key1), EVMC_ACCESS_WARM);
    EXPECT_EQ(s.access_storage(a, key2), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(a, key2), EVMC_ACCESS_WARM);
    EXPECT_EQ(s.access_storage(b, key2), EVMC_ACCESS_COLD);
    EXPECT_EQ(s.access_storage(b, key2), EVMC_ACCESS_WARM);
}

TYPED_TEST(ValueStoreTest, copy)
{
    TypeParam db{};
    db.create(a, {});
    db.create(a, key1, value1);
    db.create(a, key2, value2);
    db.create(c, {});
    db.create(c, key1, value1);
    db.create(c, key2, value2);
    db.commit();
    ValueStore s{db};

    auto t = typename decltype(s)::WorkingCopy{s};
    auto r = typename decltype(s)::WorkingCopy{s};

    EXPECT_EQ(r.access_storage(a, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(r.access_storage(b, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(r.set_storage(a, key1, value1), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(r.set_storage(c, key1, null), EVMC_STORAGE_DELETED);

    EXPECT_EQ(t.access_storage(a, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(t.access_storage(b, key1), EVMC_ACCESS_COLD);
    EXPECT_EQ(t.set_storage(a, key1, value1), EVMC_STORAGE_ASSIGNED);
    EXPECT_EQ(t.set_storage(b, key1, value2), EVMC_STORAGE_ADDED);
}

TYPED_TEST(ValueStoreTest, get_storage)
{
    using diff_t = typename ValueStore<TypeParam>::diff_t;

    TypeParam db{};
    db.create(a, {});
    db.create(a, key1, value1);
    db.create(a, key2, value2);
    db.create(b, {});
    db.create(b, key1, value1);
    db.commit();

    ValueStore t{db};
    t.merged_.storage_[a].emplace(key2, diff_t{value2, value3});
    t.merged_.deleted_storage_[b].emplace(value1, key1);

    auto s = typename decltype(t)::WorkingCopy{t};

    EXPECT_EQ(s.get_storage(a, key1), value1);
    EXPECT_EQ(s.get_storage(a, key2), value3);
    EXPECT_EQ(s.get_storage(a, key3), null);
    EXPECT_EQ(s.get_storage(b, key1), null);
}

TYPED_TEST(ValueStoreTest, set_add_delete_touched)
{
    TypeParam db{};
    ValueStore t{db};

    auto s = typename decltype(t)::WorkingCopy{t};

    EXPECT_EQ(s.set_storage(a, key1, value1), EVMC_STORAGE_ADDED);
    EXPECT_EQ(s.get_storage(a, key1), value1);
    EXPECT_EQ(s.set_storage(a, key1, null), EVMC_STORAGE_ADDED_DELETED);
    EXPECT_EQ(s.get_storage(a, key1), null);
    EXPECT_EQ(s.set_storage(a, key1, value2), EVMC_STORAGE_ADDED);
}

TYPED_TEST(ValueStoreTest, set_modify_delete_storage)
{
    TypeParam db{};
    ValueStore t{db};
    db.create(a, {});
    db.create(a, key1, value1);
    db.create(a, key2, value2);
    db.commit();

    auto s = typename decltype(t)::WorkingCopy{t};

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

TYPED_TEST(ValueStoreTest, set_modify_delete_merged)
{
    using diff_t = typename ValueStore<TypeParam>::diff_t;

    TypeParam db{};
    db.create(a, {});
    db.create(a, key1, value1);
    db.create(a, key2, value2);
    db.commit();

    ValueStore t{db};
    t.merged_.storage_[a].emplace(key1, diff_t{value1, value2});
    t.merged_.storage_[a].emplace(key2, diff_t{value2, value1});

    auto s = typename decltype(t)::WorkingCopy{t};

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

TYPED_TEST(ValueStoreTest, multiple_get_and_set_from_storage)
{
    TypeParam db{};
    ValueStore t{db};
    db.create(a, {});
    db.create(a, key1, value1);
    db.create(a, key2, value2);
    db.create(b, {});
    db.create(b, key1, value1);
    db.create(b, key2, value2);
    db.create(c, {});
    db.create(c, key1, value1);
    db.create(c, key2, value2);
    db.commit();

    auto s = typename decltype(t)::WorkingCopy{t};

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

TYPED_TEST(ValueStoreTest, multiple_get_and_set_from_merged)
{
    using diff_t = typename ValueStore<TypeParam>::diff_t;

    TypeParam db{};
    db.create(a, {});
    db.create(a, key1, value1);
    db.create(a, key2, value2);
    db.create(c, {});
    db.create(c, key1, value1);
    db.create(c, key2, value2);
    db.commit();

    ValueStore t{db};
    t.merged_.storage_[a].emplace(key1, diff_t{value1, value2});
    t.merged_.storage_[c].emplace(key1, diff_t{value1, value2});

    auto s = typename decltype(t)::WorkingCopy{t};

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

TYPED_TEST(ValueStoreTest, revert)
{
    TypeParam db{};
    ValueStore t{db};

    auto s = typename decltype(t)::WorkingCopy{t};

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

TYPED_TEST(ValueStoreTest, can_merge)
{
    TypeParam db{};
    db.create(a, {});
    db.create(a, key1, value1);
    db.create(a, key2, value2);
    db.create(b, {});
    db.create(b, key1, value1);
    db.create(b, key2, value2);
    db.commit();
    ValueStore s{db};

    auto t = typename decltype(s)::WorkingCopy{s};

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

TYPED_TEST(ValueStoreTest, can_merge_added)
{
    TypeParam db{};
    ValueStore s{db};

    auto t = typename decltype(s)::WorkingCopy{s};

    EXPECT_EQ(t.set_storage(c, key2, value1), EVMC_STORAGE_ADDED);
    EXPECT_TRUE(s.can_merge(t));
}

TYPED_TEST(ValueStoreTest, can_merge_deleted)
{
    TypeParam db{};
    db.create(a, {});
    db.create(a, key2, value2);
    db.commit();
    ValueStore s{db};

    auto t = typename decltype(s)::WorkingCopy{s};

    EXPECT_EQ(t.set_storage(a, key2, null), EVMC_STORAGE_DELETED);
    EXPECT_TRUE(s.can_merge(t));
}

TYPED_TEST(ValueStoreTest, can_merge_modified)
{
    TypeParam db{};
    db.create(a, {});
    db.create(a, key1, value1);
    db.commit();
    ValueStore s{db};

    auto t = typename decltype(s)::WorkingCopy{s};

    EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);
    EXPECT_TRUE(s.can_merge(t));
}

TYPED_TEST(ValueStoreTest, can_merge_modify_merged_added)
{
    TypeParam db{};
    ValueStore s{db};

    {
        auto t = typename decltype(s)::WorkingCopy{s};

        EXPECT_EQ(t.set_storage(c, key2, value1), EVMC_STORAGE_ADDED);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
    }
    {
        auto t = typename decltype(s)::WorkingCopy{s};
        EXPECT_EQ(t.set_storage(c, key2, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
    }
}

TYPED_TEST(ValueStoreTest, can_merge_delete_merged_added)
{
    TypeParam db{};
    ValueStore s{db};

    {
        auto t = typename decltype(s)::WorkingCopy{s};
        EXPECT_EQ(t.set_storage(c, key2, value1), EVMC_STORAGE_ADDED);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
    }
    {
        auto t = typename decltype(s)::WorkingCopy{s};
        EXPECT_EQ(t.set_storage(c, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
    }
}

TYPED_TEST(ValueStoreTest, can_merge_add_on_merged_deleted)
{
    TypeParam db{};
    db.create(a, {});
    db.create(a, key2, value2);
    db.commit();
    ValueStore s{db};

    {
        auto t = typename decltype(s)::WorkingCopy{s};
        EXPECT_EQ(t.set_storage(a, key2, null), EVMC_STORAGE_DELETED);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
    }
    {
        auto t = typename decltype(s)::WorkingCopy{s};
        EXPECT_EQ(t.set_storage(a, key2, value1), EVMC_STORAGE_ADDED);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
    }
}

TYPED_TEST(ValueStoreTest, can_merge_delete_merged_modified)
{
    TypeParam db{};
    db.create(a, {});
    db.create(a, key1, value1);
    db.commit();
    ValueStore s{db};

    {
        auto t = typename decltype(s)::WorkingCopy{s};
        EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
    }
    {
        auto t = typename decltype(s)::WorkingCopy{s};
        EXPECT_EQ(t.set_storage(a, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
        {
            auto r = typename decltype(s)::WorkingCopy{s};
            EXPECT_EQ(r.get_storage(a, key1), null);
        }
    }
}

TYPED_TEST(ValueStoreTest, cant_merge_colliding_merge)
{
    using diff_t = typename ValueStore<TypeParam>::diff_t;

    TypeParam db{};
    db.create(a, {});
    db.create(a, key1, value1);
    db.commit();
    ValueStore s{db};

    auto t = typename decltype(s)::WorkingCopy{s};

    EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);

    s.merged_.storage_[a].emplace(key1, diff_t{value1, value2});

    EXPECT_FALSE(s.can_merge(t));
}

TYPED_TEST(ValueStoreTest, cant_merge_deleted_merge)
{
    TypeParam db{};
    db.create(a, {});
    db.create(a, key1, value1);
    db.commit();
    ValueStore s{db};

    auto t = typename decltype(s)::WorkingCopy{s};

    EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);

    s.merged_.deleted_storage_[a].insert(deleted_key{value1, key1});

    EXPECT_FALSE(s.can_merge(t));
}

TYPED_TEST(ValueStoreTest, cant_merge_conflicting_adds)
{
    using diff_t = typename ValueStore<TypeParam>::diff_t;

    TypeParam db{};
    ValueStore s{db};

    auto t = typename decltype(s)::WorkingCopy{s};

    EXPECT_EQ(t.set_storage(a, key1, value1), EVMC_STORAGE_ADDED);

    s.merged_.storage_[a].emplace(key1, diff_t{{}, value2});

    EXPECT_FALSE(s.can_merge(t));
}

TYPED_TEST(ValueStoreTest, cant_merge_conflicting_modifies)
{
    using diff_t = typename ValueStore<TypeParam>::diff_t;

    TypeParam db{};
    db.create(a, {});
    db.create(a, key1, value3);
    db.commit();
    ValueStore s{db};

    auto t = typename decltype(s)::WorkingCopy{s};

    EXPECT_EQ(t.set_storage(a, key1, value1), EVMC_STORAGE_MODIFIED);

    s.merged_.storage_[a].emplace(key1, diff_t{value3, value2});

    EXPECT_FALSE(s.can_merge(t));
}

TYPED_TEST(ValueStoreTest, cant_merge_conflicting_deleted)
{
    TypeParam db{};
    db.create(a, {});
    db.create(a, key1, value1);
    db.commit();
    ValueStore s{db};

    auto t = typename decltype(s)::WorkingCopy{s};

    EXPECT_EQ(t.set_storage(a, key1, null), EVMC_STORAGE_DELETED);

    s.merged_.deleted_storage_[a].insert({value1, key1});

    EXPECT_FALSE(s.can_merge(t));
}

TYPED_TEST(ValueStoreTest, cant_merge_delete_conflicts_with_modify)
{
    using diff_t = typename ValueStore<TypeParam>::diff_t;

    TypeParam db{};
    db.create(a, {});
    db.create(a, key1, value1);
    db.commit();
    ValueStore s{db};

    auto t = typename decltype(s)::WorkingCopy{s};

    EXPECT_EQ(t.set_storage(a, key1, null), EVMC_STORAGE_DELETED);

    s.merged_.storage_[a].emplace(key1, diff_t{value1, value2});

    EXPECT_FALSE(s.can_merge(t));
}

TYPED_TEST(ValueStoreTest, merge_touched_multiple)
{
    TypeParam db{};
    db.create(a, {});
    db.create(a, key1, value1);
    db.create(b, {});
    db.create(b, key1, value1);
    db.commit();
    ValueStore s{db};

    {
        auto t = typename decltype(s)::WorkingCopy{s};

        EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(t.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(t.set_storage(c, key1, value1), EVMC_STORAGE_ADDED);

        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
    }

    {
        auto u = typename decltype(s)::WorkingCopy{s};

        EXPECT_EQ(u.set_storage(a, key1, value3), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(u.set_storage(b, key1, value1), EVMC_STORAGE_ADDED);
        EXPECT_EQ(u.set_storage(c, key1, null), EVMC_STORAGE_DELETED);

        EXPECT_TRUE(s.can_merge(u));
        s.merge_touched(u);
    }
}

TYPED_TEST(ValueStoreTest, can_commit)
{
    TypeParam db{};
    db.create(a, {});
    db.create(a, key1, value1);
    db.create(b, {});
    db.create(b, key1, value1);
    db.commit();
    ValueStore s{db};

    {
        auto t = typename decltype(s)::WorkingCopy{s};

        EXPECT_EQ(t.set_storage(a, key1, value2), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(t.set_storage(b, key1, null), EVMC_STORAGE_DELETED);
        EXPECT_EQ(t.set_storage(c, key1, value1), EVMC_STORAGE_ADDED);

        EXPECT_TRUE(s.can_merge(t));
        s.merge_touched(t);
        EXPECT_TRUE(s.can_commit());
    }

    {
        auto u = typename decltype(s)::WorkingCopy{s};

        EXPECT_EQ(u.set_storage(a, key1, value3), EVMC_STORAGE_MODIFIED);
        EXPECT_EQ(u.set_storage(b, key1, value1), EVMC_STORAGE_ADDED);
        EXPECT_EQ(u.set_storage(c, key1, null), EVMC_STORAGE_DELETED);

        EXPECT_TRUE(s.can_merge(u));
        s.merge_touched(u);
        EXPECT_TRUE(s.can_commit());
    }
}

TYPED_TEST(ValueStoreTest, can_commit_restored)
{
    TypeParam db{};
    db.create(a, {});
    db.create(a, key1, value1);
    db.create(b, {});
    db.create(b, key1, value1);
    db.commit();
    ValueStore s{db};

    {
        auto t = typename decltype(s)::WorkingCopy{s};
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
        auto u = typename decltype(s)::WorkingCopy{s};
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

TYPED_TEST(ValueStoreTest, commit_all_merged)
{
    TypeParam db{};
    db.create(a, {});
    db.create(a, key1, value1);
    db.create(b, {});
    db.create(b, key1, value1);
    db.commit();
    ValueStore s{db};

    {
        auto t = typename decltype(s)::WorkingCopy{s};
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
        auto u = typename decltype(s)::WorkingCopy{s};
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

    s.commit_all_merged();
}
