#include <gtest/gtest.h>

#include <monad/db/in_memory_db.hpp>
#include <monad/db/in_memory_trie_db.hpp>
#include <monad/db/rocks_db.hpp>
#include <monad/db/rocks_trie_db.hpp>
#include <monad/logging/formatter.hpp>
#include <monad/state/state_changes.hpp>

using namespace monad;
using namespace monad::db;

static constexpr auto a = 0x5353535353535353535353535353535353535353_address;
static constexpr auto b = 0xbebebebebebebebebebebebebebebebebebebebe_address;
static constexpr auto hash1 =
    0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
static constexpr auto key1 =
    0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
static constexpr auto key2 =
    0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
static constexpr auto value1 =
    0x0000000000000013370000000000000000000000000000000000000000000003_bytes32;
static constexpr auto value2 =
    0x0000000000000000000000000000000000000000000000000000000000000007_bytes32;

template <typename TDB>
struct DBTest : public testing::Test
{
};
using DBTypes =
    ::testing::Types<InMemoryDB, RocksDB, InMemoryTrieDB, RocksTrieDB>;
TYPED_TEST_SUITE(DBTest, DBTypes);

template <typename TDB>
struct TrieDBTest : public testing::Test
{
};
using TrieDBTypes = ::testing::Types<InMemoryTrieDB, RocksTrieDB>;
TYPED_TEST_SUITE(TrieDBTest, TrieDBTypes);

TYPED_TEST(DBTest, storage_creation)
{
    TypeParam db;
    Account acct{.balance = 1'000'000, .code_hash = hash1, .nonce = 1337};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct}},
        .storage_changes = {{a, {{key1, value1}}}}});

    EXPECT_TRUE(db.contains(a, key1));
    EXPECT_EQ(db.at(a, key1), value1);

    db.commit(state::StateChanges{
        .account_changes = {{b, acct}}, .storage_changes = {}});
    EXPECT_TRUE(db.contains(b));

    db.commit(state::StateChanges{
        .account_changes = {}, .storage_changes = {{b, {{key1, value1}}}}});
    EXPECT_TRUE(db.contains(b, key1));
    EXPECT_EQ(db.at(b, key1), value1);
}

TEST(InMemoryTrieDB, account_creation)
{
    InMemoryTrieDB db;
    Account acct{.balance = 1'000'000, .code_hash = hash1, .nonce = 1337};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct}}, .storage_changes = {}});

    EXPECT_EQ(db.accounts().leaves_storage.size(), 1);
    EXPECT_EQ(db.accounts().trie_storage.size(), 1);

    EXPECT_TRUE(db.contains(a));
    EXPECT_EQ(db.at(a), acct);
}

TYPED_TEST(DBTest, query)
{
    TypeParam db;
    Account acct{.balance = 1'000'000, .code_hash = hash1, .nonce = 1337};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct}},
        .storage_changes = {{a, {{key1, value1}, {key2, value2}}}}});

    EXPECT_EQ(db.query(a), acct);
    EXPECT_FALSE(db.query(b).has_value());
    EXPECT_EQ(db.query(a, key1), value1);
    EXPECT_EQ(db.query(a, key2), value2);
}

TEST(InMemoryTrieDB, erase)
{
    InMemoryTrieDB db;
    Account acct{.balance = 1'000'000, .code_hash = hash1, .nonce = 1337};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct}},
        .storage_changes = {{a, {{key1, value1}, {key2, value2}}}}});

    EXPECT_EQ(
        db.root_hash(a),
        0x3f9802e4f21fce3d2b07d21c8f2b60b22f7c745c455e752728030580177f8e11_bytes32);
    EXPECT_EQ(
        db.root_hash(),
        0x3f7578fb3acc297f8847c7885717733b268cb52dc6b8e5a68aff31c254b6b5b3_bytes32);

    db.commit(state::StateChanges{
        .account_changes = {{a, std::nullopt}},
        .storage_changes = {{a, {{key1, value2}, {key2, value1}}}}});

    EXPECT_FALSE(db.contains(a));
    EXPECT_FALSE(db.contains(a, key1));
    EXPECT_FALSE(db.contains(a, key2));
    EXPECT_TRUE(db.accounts().leaves_storage.empty());
    EXPECT_TRUE(db.accounts().trie_storage.empty());
    EXPECT_TRUE(db.storage().leaves_storage.empty());
    EXPECT_TRUE(db.storage().trie_storage.empty());

    EXPECT_EQ(db.root_hash(), NULL_ROOT);
    EXPECT_EQ(db.root_hash(a), NULL_ROOT);
}

TYPED_TEST(TrieDBTest, ModifyStorageOfAccount)
{
    TypeParam db;
    Account acct{.balance = 1'000'000, .code_hash = hash1, .nonce = 1337};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct}},
        .storage_changes = {{a, {{key1, value1}, {key2, value2}}}}});

    db.commit(state::StateChanges{
        .account_changes = {}, .storage_changes = {{a, {{key2, value1}}}}});

    EXPECT_EQ(
        db.root_hash(),
        0x0169f0b22c30d7d6f0bb7ea2a07be178e216b72f372a6a7bafe55602e5650e60_bytes32);
}
