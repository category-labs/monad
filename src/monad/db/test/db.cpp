#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <monad/db/in_memory_db.hpp>
#include <monad/db/in_memory_trie_db.hpp>
#include <monad/db/rocks_db.hpp>
#include <monad/db/rocks_trie_db.hpp>
#include <monad/logging/formatter.hpp>
#include <monad/state/state_changes.hpp>
#include <monad/test/hijacked_db.hpp>
#include <monad/test/make_db.hpp>

using namespace monad;
using namespace monad::db;

// clang-format off
template<typename T>
concept Trie = requires(T a)
{
    { a.root_hash() } -> std::convertible_to<bytes32_t>;
    { a.root_hash(address_t{}) } -> std::convertible_to<bytes32_t>;
};
// clang-format on

static constexpr auto a = 0x5353535353535353535353535353535353535353_address;
static constexpr auto b = 0xbebebebebebebebebebebebebebebebebebebebe_address;
static constexpr auto key1 =
    0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
static constexpr auto key2 =
    0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
static constexpr auto value1 =
    0x0000000000000013370000000000000000000000000000000000000000000003_bytes32;
static constexpr auto value2 =
    0x0000000000000000000000000000000000000000000000000000000000000007_bytes32;
static constexpr auto code1 = byte_string{0xab, 0xcd, 0xef};
static constexpr auto code2 = byte_string{0xbb, 0xbb, 0xbb};
static constexpr auto code_hash1 =
    0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
static constexpr auto code_hash2 =
    0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1bbbbbbbbb_bytes32;

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

template <typename TDB>
struct HijackedExecutionDBTest : public testing::Test
{
};
using HijackedExecutionDBTypes = ::testing::Types<
    monad::test::hijacked::InMemoryDB, monad::test::hijacked::InMemoryTrieDB,
    monad::test::hijacked::RocksDB, monad::test::hijacked::RocksTrieDB>;
TYPED_TEST_SUITE(HijackedExecutionDBTest, HijackedExecutionDBTypes);

template <typename TDB>
struct RocksDBTest : public testing::Test
{
};
using RocksDBTypes = ::testing::Types<RocksDB, RocksTrieDB>;
TYPED_TEST_SUITE(RocksDBTest, RocksDBTypes);

template <typename TDB>
struct ReadWriteTest : public testing::Test
{
};
using ReadWriteTypes = ::testing::Types<
    std::pair<ReadOnlyRocksDB, RocksDB>,
    std::pair<ReadOnlyRocksTrieDB, RocksTrieDB>>;
TYPED_TEST_SUITE(ReadWriteTest, ReadWriteTypes);

TYPED_TEST(HijackedExecutionDBTest, executor)
{
    test::hijacked::Executor::EXECUTED = false;
    auto db = test::make_db<TypeParam>();
    EXPECT_FALSE(test::hijacked::Executor::EXECUTED);

    Account acct{.balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct}},
        .storage_changes = {{a, {{key1, value1}}}},
        .code_changes = {{code_hash1, code1}}});

    test::hijacked::Executor::EXECUTED = false;
    (void)db.try_find(a);
    EXPECT_TRUE(test::hijacked::Executor::EXECUTED);

    test::hijacked::Executor::EXECUTED = false;
    (void)db.at(a);
    EXPECT_TRUE(test::hijacked::Executor::EXECUTED);

    test::hijacked::Executor::EXECUTED = false;
    (void)db.contains(a);
    EXPECT_TRUE(test::hijacked::Executor::EXECUTED);

    test::hijacked::Executor::EXECUTED = false;
    (void)db.try_find(a, key1);
    EXPECT_TRUE(test::hijacked::Executor::EXECUTED);

    test::hijacked::Executor::EXECUTED = false;
    (void)db.at(a, key1);
    EXPECT_TRUE(test::hijacked::Executor::EXECUTED);

    test::hijacked::Executor::EXECUTED = false;
    (void)db.contains(a, key1);
    EXPECT_TRUE(test::hijacked::Executor::EXECUTED);

    test::hijacked::Executor::EXECUTED = false;
    (void)db.try_find(code_hash1);
    EXPECT_TRUE(test::hijacked::Executor::EXECUTED);

    test::hijacked::Executor::EXECUTED = false;
    (void)db.at(code_hash1);
    EXPECT_TRUE(test::hijacked::Executor::EXECUTED);

    test::hijacked::Executor::EXECUTED = false;
    (void)db.contains(code_hash1);
    EXPECT_TRUE(test::hijacked::Executor::EXECUTED);
}

TYPED_TEST(DBTest, storage_creation)
{
    auto db = test::make_db<TypeParam>();
    Account acct{.balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};
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

TYPED_TEST(DBTest, storage_try_find)
{
    auto db = test::make_db<TypeParam>();
    Account acct{.nonce = 1};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct}},
        .storage_changes = {{a, {{key1, value1}}}},
    });

    // Existing key
    EXPECT_TRUE(db.contains(a, key1));
    EXPECT_EQ(db.try_find(a, key1), value1);

    // Non-existing key
    EXPECT_FALSE(db.contains(a, key2));
    EXPECT_EQ(db.try_find(a, key2), bytes32_t{});

    // Non-existing account
    EXPECT_FALSE(db.contains(b));
    EXPECT_EQ(db.try_find(b, key1), bytes32_t{});
}

TYPED_TEST(DBTest, code_creation)
{
    auto db = test::make_db<TypeParam>();
    Account acct_a{.balance = 1, .code_hash = code_hash1, .nonce = 1};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct_a}},
        .storage_changes = {},
        .code_changes = {{code_hash1, code1}},
    });

    EXPECT_TRUE(db.contains(code_hash1));
    EXPECT_EQ(db.at(code_hash1), code1);

    Account acct_b{.balance = 0, .code_hash = code_hash2, .nonce = 1};
    db.commit(state::StateChanges{
        .account_changes = {{b, acct_b}},
        .storage_changes = {},
        .code_changes = {{code_hash2, code2}}});

    EXPECT_TRUE(db.contains(code_hash2));
    EXPECT_EQ(db.at(code_hash2), code2);
}

TYPED_TEST(DBTest, code_try_find)
{
    auto db = test::make_db<TypeParam>();
    Account acct_a{.balance = 1, .code_hash = code_hash1, .nonce = 1};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct_a}},
        .storage_changes = {},
        .code_changes = {{code_hash1, code1}},
    });

    EXPECT_TRUE(db.contains(code_hash1));
    EXPECT_EQ(db.try_find(code_hash1), code1);
}

TEST(InMemoryTrieDB, account_creation)
{
    auto db = test::make_db<InMemoryTrieDB>();
    Account acct{.balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct}}, .storage_changes = {}});

    EXPECT_EQ(db.accounts().leaves_storage.size(), 1);
    EXPECT_EQ(db.accounts().trie_storage.size(), 1);

    EXPECT_TRUE(db.contains(a));
    EXPECT_EQ(db.at(a), acct);
}

TEST(InMemoryTrieDB, erase)
{
    auto db = test::make_db<InMemoryTrieDB>();
    Account acct{.balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};
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
    auto db = test::make_db<TypeParam>();
    Account acct{.balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct}},
        .storage_changes = {{a, {{key1, value1}, {key2, value2}}}}});

    db.commit(state::StateChanges{
        .account_changes = {}, .storage_changes = {{a, {{key2, value1}}}}});

    EXPECT_EQ(
        db.root_hash(),
        0x0169f0b22c30d7d6f0bb7ea2a07be178e216b72f372a6a7bafe55602e5650e60_bytes32);
}

TYPED_TEST(RocksDBTest, block_history_for_constructor_with_start_block_number)
{
    constexpr auto BLOCK_HISTORY = 100ull;
    auto block_number = 0ull;
    auto const root = test::make_db_root(
        *testing::UnitTest::GetInstance()->current_test_info());
    Account const acct{
        .balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};

    {
        auto db = TypeParam{root, block_number, BLOCK_HISTORY};

        Account acct{
            .balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};
        db.commit(state::StateChanges{
            .account_changes = {{a, acct}},
            .storage_changes = {{a, {{key1, value1}, {key2, value2}}}}});
        db.create_and_prune_block_history(block_number++);

        EXPECT_EQ(db.try_find(a), acct);
        EXPECT_EQ(db.try_find(a, key1), value1);
        EXPECT_EQ(db.try_find(a, key2), value2);

        if constexpr (Trie<TypeParam>) {
            EXPECT_EQ(
                db.root_hash(a),
                0x3f9802e4f21fce3d2b07d21c8f2b60b22f7c745c455e752728030580177f8e11_bytes32);
            EXPECT_EQ(
                db.root_hash(),
                0x3f7578fb3acc297f8847c7885717733b268cb52dc6b8e5a68aff31c254b6b5b3_bytes32);
        }

        EXPECT_EQ(db.starting_block_number, block_number - 1u);
    }

    {
        auto db = TypeParam{root, block_number, BLOCK_HISTORY};

        EXPECT_EQ(db.try_find(a), acct);
        EXPECT_EQ(db.try_find(a, key1), value1);
        EXPECT_EQ(db.try_find(a, key2), value2);

        if constexpr (Trie<TypeParam>) {
            EXPECT_EQ(
                db.root_hash(a),
                0x3f9802e4f21fce3d2b07d21c8f2b60b22f7c745c455e752728030580177f8e11_bytes32);
            EXPECT_EQ(
                db.root_hash(),
                0x3f7578fb3acc297f8847c7885717733b268cb52dc6b8e5a68aff31c254b6b5b3_bytes32);
        }

        db.commit(state::StateChanges{
            .account_changes = {}, .storage_changes = {{a, {{key2, value1}}}}});
        db.create_and_prune_block_history(block_number++);

        EXPECT_EQ(db.try_find(a), acct);
        EXPECT_EQ(db.try_find(a, key1), value1);
        EXPECT_EQ(db.try_find(a, key2), value1);

        if constexpr (Trie<TypeParam>) {
            EXPECT_EQ(
                db.root_hash(),
                0x0169f0b22c30d7d6f0bb7ea2a07be178e216b72f372a6a7bafe55602e5650e60_bytes32);
        }
        EXPECT_EQ(db.starting_block_number, block_number - 1u);
    }

    {
        auto db = TypeParam{root, block_number, BLOCK_HISTORY};
        EXPECT_EQ(db.try_find(a), acct);
        EXPECT_EQ(db.try_find(a, key1), value1);
        EXPECT_EQ(db.try_find(a, key2), value1);

        if constexpr (Trie<TypeParam>) {
            EXPECT_EQ(
                db.root_hash(),
                0x0169f0b22c30d7d6f0bb7ea2a07be178e216b72f372a6a7bafe55602e5650e60_bytes32);
        }
        EXPECT_EQ(db.starting_block_number, block_number);
    }

    {
        auto db = TypeParam{root, block_number - 1, BLOCK_HISTORY};

        EXPECT_EQ(db.try_find(a), acct);
        EXPECT_EQ(db.try_find(a, key1), value1);
        EXPECT_EQ(db.try_find(a, key2), value2);

        if constexpr (Trie<TypeParam>) {
            EXPECT_EQ(
                db.root_hash(a),
                0x3f9802e4f21fce3d2b07d21c8f2b60b22f7c745c455e752728030580177f8e11_bytes32);
            EXPECT_EQ(
                db.root_hash(),
                0x3f7578fb3acc297f8847c7885717733b268cb52dc6b8e5a68aff31c254b6b5b3_bytes32);
        }

        EXPECT_EQ(db.starting_block_number, block_number - 1u);
    }
}

TYPED_TEST(
    RocksDBTest, block_history_for_constructor_without_start_block_number)
{
    constexpr auto BLOCK_HISTORY = 100ull;
    auto block_number = 0ull;
    auto const root = test::make_db_root(
        *testing::UnitTest::GetInstance()->current_test_info());
    Account const acct{
        .balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};

    {
        auto db = TypeParam{root, BLOCK_HISTORY};

        Account acct{
            .balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};
        db.commit(state::StateChanges{
            .account_changes = {{a, acct}},
            .storage_changes = {{a, {{key1, value1}, {key2, value2}}}}});
        db.create_and_prune_block_history(block_number++);

        EXPECT_EQ(db.try_find(a), acct);
        EXPECT_EQ(db.try_find(a, key1), value1);
        EXPECT_EQ(db.try_find(a, key2), value2);

        if constexpr (Trie<TypeParam>) {
            EXPECT_EQ(
                db.root_hash(a),
                0x3f9802e4f21fce3d2b07d21c8f2b60b22f7c745c455e752728030580177f8e11_bytes32);
            EXPECT_EQ(
                db.root_hash(),
                0x3f7578fb3acc297f8847c7885717733b268cb52dc6b8e5a68aff31c254b6b5b3_bytes32);
        }
        EXPECT_EQ(db.starting_block_number, block_number - 1u);
    }

    {
        auto db = TypeParam{root, BLOCK_HISTORY};

        EXPECT_EQ(db.try_find(a), acct);
        EXPECT_EQ(db.try_find(a, key1), value1);
        EXPECT_EQ(db.try_find(a, key2), value2);

        if constexpr (Trie<TypeParam>) {
            EXPECT_EQ(
                db.root_hash(a),
                0x3f9802e4f21fce3d2b07d21c8f2b60b22f7c745c455e752728030580177f8e11_bytes32);
            EXPECT_EQ(
                db.root_hash(),
                0x3f7578fb3acc297f8847c7885717733b268cb52dc6b8e5a68aff31c254b6b5b3_bytes32);
        }

        db.commit(state::StateChanges{
            .account_changes = {}, .storage_changes = {{a, {{key2, value1}}}}});
        db.create_and_prune_block_history(block_number++);

        EXPECT_EQ(db.try_find(a), acct);
        EXPECT_EQ(db.try_find(a, key1), value1);
        EXPECT_EQ(db.try_find(a, key2), value1);

        if constexpr (Trie<TypeParam>) {
            EXPECT_EQ(
                db.root_hash(),
                0x0169f0b22c30d7d6f0bb7ea2a07be178e216b72f372a6a7bafe55602e5650e60_bytes32);
        }

        EXPECT_EQ(db.starting_block_number, block_number - 1u);
    }

    {
        auto db = TypeParam{root, BLOCK_HISTORY};

        EXPECT_EQ(db.try_find(a), acct);
        EXPECT_EQ(db.try_find(a, key1), value1);
        EXPECT_EQ(db.try_find(a, key2), value1);

        if constexpr (Trie<TypeParam>) {
            EXPECT_EQ(
                db.root_hash(),
                0x0169f0b22c30d7d6f0bb7ea2a07be178e216b72f372a6a7bafe55602e5650e60_bytes32);
        }
        EXPECT_EQ(db.starting_block_number, block_number);
    }
}

TYPED_TEST(RocksDBTest, block_history_pruning)
{
    constexpr auto BLOCK_HISTORY = 1ull;
    auto block_number = 0ull;
    auto const root = test::make_db_root(
        *testing::UnitTest::GetInstance()->current_test_info());
    Account const acct{
        .balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};

    {
        auto db = TypeParam{root, block_number, BLOCK_HISTORY};
        Account acct{
            .balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};
        db.commit(state::StateChanges{
            .account_changes = {{a, acct}},
            .storage_changes = {{a, {{key1, value1}, {key2, value2}}}}});
        db.create_and_prune_block_history(block_number++);

        db.create_and_prune_block_history(block_number++);
        db.create_and_prune_block_history(block_number++);

        EXPECT_EQ(db.try_find(a), acct);
        EXPECT_EQ(db.try_find(a, key1), value1);
        EXPECT_EQ(db.try_find(a, key2), value2);

        if constexpr (Trie<TypeParam>) {
            EXPECT_EQ(
                db.root_hash(a),
                0x3f9802e4f21fce3d2b07d21c8f2b60b22f7c745c455e752728030580177f8e11_bytes32);
            EXPECT_EQ(
                db.root_hash(),
                0x3f7578fb3acc297f8847c7885717733b268cb52dc6b8e5a68aff31c254b6b5b3_bytes32);
        }
    }

    {
        auto db = TypeParam{root, block_number, BLOCK_HISTORY};

        EXPECT_EQ(db.try_find(a), acct);
        EXPECT_EQ(db.try_find(a, key1), value1);
        EXPECT_EQ(db.try_find(a, key2), value2);

        if constexpr (Trie<TypeParam>) {
            EXPECT_EQ(
                db.root_hash(a),
                0x3f9802e4f21fce3d2b07d21c8f2b60b22f7c745c455e752728030580177f8e11_bytes32);
            EXPECT_EQ(
                db.root_hash(),
                0x3f7578fb3acc297f8847c7885717733b268cb52dc6b8e5a68aff31c254b6b5b3_bytes32);
        }
    }

    EXPECT_THROW(
        [&]() {
            auto const b = block_number - 1;
            try {
                auto const db = TypeParam(root, b, BLOCK_HISTORY);
            }
            catch (std::runtime_error const &e) {
                EXPECT_THAT(
                    e.what(),
                    ::testing::MatchesRegex(fmt::format(
                        ".*starting block directory is missing {}",
                        root / std::to_string(b - 1))));
                throw;
            }
        }(),
        std::runtime_error);
}

TYPED_TEST(ReadWriteTest, read_only)
{
    using ReadOnly = typename TypeParam::first_type;
    using ReadWrite = typename TypeParam::second_type;

    auto const root = test::make_db_root(
        *testing::UnitTest::GetInstance()->current_test_info());
    Account const acct{
        .balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};

    {
        auto db = ReadWrite{root, 1};
        db.commit(state::StateChanges{
            .account_changes = {{a, acct}},
            .storage_changes = {{a, {{key1, value1}, {key2, value2}}}}});
        db.create_and_prune_block_history(0);
    }

    {
        auto db = ReadOnly{root, 1};
        EXPECT_TRUE(db.contains(a));
        EXPECT_EQ(db.try_find(a), acct);
        EXPECT_EQ(db.at(a), acct);

        EXPECT_TRUE(db.contains(a, key1));
        EXPECT_EQ(db.try_find(a, key1), value1);
        EXPECT_EQ(db.at(a, key1), value1);

        EXPECT_TRUE(db.contains(a, key2));
        EXPECT_EQ(db.try_find(a, key2), value2);
        EXPECT_EQ(db.at(a, key2), value2);

        if constexpr (Trie<ReadOnly>) {
            EXPECT_EQ(
                db.root_hash(a),
                0x3f9802e4f21fce3d2b07d21c8f2b60b22f7c745c455e752728030580177f8e11_bytes32);
            EXPECT_EQ(
                db.root_hash(),
                0x3f7578fb3acc297f8847c7885717733b268cb52dc6b8e5a68aff31c254b6b5b3_bytes32);
        }
    }
}
