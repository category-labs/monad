#include <gtest/gtest.h>
#include <monad/db/trie_db.hpp>

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
using DBTypes = ::testing::Types<InMemoryDB, InMemoryTrieDB>;
TYPED_TEST_SUITE(DBTest, DBTypes);

TYPED_TEST(DBTest, storage_creation)
{
    TypeParam db;
    Account acct{.balance = 1'000'000, .code_hash = hash1, .nonce = 1337};
    db.create(a, acct);
    db.create(a, key1, value1);
    db.commit();

    EXPECT_TRUE(db.contains(a, key1));
    EXPECT_EQ(db.at(a, key1), value1);

    db.create(b, acct);
    db.commit();
    EXPECT_TRUE(db.contains(b));

    db.create(b, key1, value1);
    db.commit();
    EXPECT_TRUE(db.contains(b, key1));
    EXPECT_EQ(db.at(b, key1), value1);
}

TYPED_TEST(DBTest, storage_update)
{
    TypeParam db;
    Account acct{.balance = 1'000'000, .code_hash = hash1, .nonce = 1337};
    db.create(a, acct);
    db.create(a, key1, value1);
    db.commit();

    EXPECT_TRUE(db.contains(a, key1));
    EXPECT_EQ(db.at(a, key1), value1);

    db.update(a, key1, value2);

    // key1 should not change until commit
    EXPECT_EQ(db.at(a, key1), value1);

    db.commit();

    EXPECT_EQ(db.at(a, key1), value2);
}

TEST(InMemoryTrieDB, account_creation)
{
    InMemoryTrieDB db;
    Account acct{.balance = 1'000'000, .code_hash = hash1, .nonce = 1337};
    db.create(a, acct);
    db.commit();

    EXPECT_EQ(db.accounts.leaves_storage.size(), 1);
    EXPECT_EQ(db.accounts.trie_storage.size(), 1);

    EXPECT_TRUE(db.contains(a));
    EXPECT_EQ(db.at(a), acct);
}

TEST(InMemoryTrieDB, erase)
{
    InMemoryTrieDB db;
    Account acct{.balance = 1'000'000, .code_hash = hash1, .nonce = 1337};
    db.create(a, acct);
    db.create(a, key1, value1);
    db.create(a, key2, value2);
    db.commit();

    db.erase(a);
    db.update(a, key1, value2);
    db.update(a, key2, value1);

    db.commit();

    EXPECT_FALSE(db.contains(a));
    EXPECT_FALSE(db.contains(a, key1));
    EXPECT_FALSE(db.contains(a, key2));
    EXPECT_TRUE(db.accounts.leaves_storage.empty());
    EXPECT_TRUE(db.accounts.trie_storage.empty());
    EXPECT_TRUE(db.storage.leaves_storage.empty());
    EXPECT_TRUE(db.storage.trie_storage.empty());
}
