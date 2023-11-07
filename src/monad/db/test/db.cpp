#include <monad/core/account.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/in_memory_old_trie_db.hpp>
#include <monad/db/in_memory_trie_db.hpp>
#include <monad/db/permission.hpp>
#include <monad/db/rocks_trie_db.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/test/make_db.hpp>

#include <evmc/evmc.hpp>

#include <quill/bundled/fmt/core.h>

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <optional>
#include <stdexcept>
#include <string>

using namespace monad;
using namespace monad::db;

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
    ::testing::Types<InMemoryOldTrieDB, RocksTrieDB, InMemoryTrieDB>;
TYPED_TEST_SUITE(DBTest, DBTypes);

template <typename TDB>
struct RocksDBTest : public testing::Test
{
};
using RocksDBTypes = ::testing::Types<RocksTrieDB>;
TYPED_TEST_SUITE(RocksDBTest, RocksDBTypes);

TYPED_TEST(DBTest, read_storage)
{
    auto db = test::make_db<TypeParam>();
    Account acct{.balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};

    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{});

    EXPECT_EQ(db.read_storage(a, key1), value1);

    db.commit(
        StateDeltas{
            {b,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{});
    EXPECT_EQ(db.read_account(b), acct);
    EXPECT_EQ(db.read_storage(b, key1), value1);
}

TYPED_TEST(DBTest, read_nonexistent_storage)
{
    auto db = test::make_db<TypeParam>();
    Account acct{.nonce = 1};
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{});

    // Non-existing key
    EXPECT_EQ(db.read_storage(a, key2), bytes32_t{});

    // Non-existing account
    EXPECT_FALSE(db.read_account(b).has_value());
    EXPECT_EQ(db.read_storage(b, key1), bytes32_t{});
}

TYPED_TEST(DBTest, read_code)
{
    auto db = test::make_db<TypeParam>();
    Account acct_a{.balance = 1, .code_hash = code_hash1, .nonce = 1};
    db.commit(
        StateDeltas{{a, StateDelta{.account = {std::nullopt, acct_a}}}},
        Code{{code_hash1, code1}});

    EXPECT_EQ(db.read_code(code_hash1), code1);

    Account acct_b{.balance = 0, .code_hash = code_hash2, .nonce = 1};
    db.commit(
        StateDeltas{{b, StateDelta{.account = {std::nullopt, acct_b}}}},
        Code{{code_hash2, code2}});

    EXPECT_EQ(db.read_code(code_hash2), code2);
}

TEST(InMemoryOldTrieDB, account_creation)
{
    auto db = test::make_db<InMemoryOldTrieDB>();
    Account acct{.balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};
    db.commit(
        StateDeltas{{a, StateDelta{.account = {std::nullopt, acct}}}}, Code{});

    EXPECT_EQ(db.accounts_trie.leaves_storage.size(), 1);
    EXPECT_EQ(db.accounts_trie.trie_storage.size(), 1);
    EXPECT_EQ(db.read_account(a), acct);
}

TEST(InMemoryOldTrieDB, erase)
{
    auto db = test::make_db<InMemoryOldTrieDB>();
    Account acct{.balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}}},
        Code{});

    EXPECT_EQ(
        db.storage_root(a),
        0x3f9802e4f21fce3d2b07d21c8f2b60b22f7c745c455e752728030580177f8e11_bytes32);
    EXPECT_EQ(
        db.state_root(),
        0x3f7578fb3acc297f8847c7885717733b268cb52dc6b8e5a68aff31c254b6b5b3_bytes32);

    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {acct, std::nullopt},
                 .storage =
                     {{key1, {value1, value2}}, {key2, {value2, value1}}}}}},
        Code{});

    EXPECT_EQ(db.read_storage(a, key1), bytes32_t{});
    EXPECT_EQ(db.read_storage(a, key2), bytes32_t{});
    EXPECT_TRUE(db.accounts_trie.leaves_storage.empty());
    EXPECT_TRUE(db.accounts_trie.trie_storage.empty());
    EXPECT_TRUE(db.storage_trie.leaves_storage.empty());
    EXPECT_TRUE(db.storage_trie.trie_storage.empty());

    EXPECT_EQ(db.state_root(), NULL_ROOT);
    EXPECT_EQ(db.storage_root(a), NULL_ROOT);
}

TYPED_TEST(DBTest, ModifyStorageOfAccount)
{
    // TODO: remove when state root functionality is implemented
    if (std::same_as<TypeParam, InMemoryTrieDB>) {
        GTEST_SKIP();
    }
    auto db = test::make_db<TypeParam>();
    Account acct{.balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}}},
        Code{});
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {acct, acct},
                 .storage = {{key2, {value2, value1}}}}}},
        Code{});

    EXPECT_EQ(
        db.state_root(),
        0x0169f0b22c30d7d6f0bb7ea2a07be178e216b72f372a6a7bafe55602e5650e60_bytes32);
}

TYPED_TEST(DBTest, touch_without_modify_regression)
{
    // TODO: remove when state root functionality is implemented
    if (std::same_as<TypeParam, InMemoryTrieDB>) {
        GTEST_SKIP();
    }
    auto db = test::make_db<TypeParam>();
    db.commit(
        StateDeltas{{a, StateDelta{.account = {std::nullopt, std::nullopt}}}},
        Code{});

    EXPECT_EQ(db.read_account(a), std::nullopt);
    EXPECT_EQ(db.state_root(), NULL_ROOT);
}

TYPED_TEST(DBTest, delete_account_modify_storage_regression)
{
    // TODO: remove when state root functionality is implemented
    if (std::same_as<TypeParam, InMemoryTrieDB>) {
        GTEST_SKIP();
    }
    auto db = test::make_db<TypeParam>();
    Account acct{.balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}}},
        Code{});

    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {acct, std::nullopt},
                 .storage =
                     {{key1, {value1, value2}}, {key2, {value2, value1}}}}}},
        Code{});

    EXPECT_EQ(db.read_account(a), std::nullopt);
    EXPECT_EQ(db.read_storage(a, key1), bytes32_t{});
    EXPECT_EQ(db.state_root(), NULL_ROOT);
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
        auto db = TypeParam{db::Writable{}, root, block_number, BLOCK_HISTORY};

        Account acct{
            .balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};
        db.commit(
            StateDeltas{
                {a,
                 StateDelta{
                     .account = {std::nullopt, acct},
                     .storage =
                         {{key1, {bytes32_t{}, value1}},
                          {key2, {bytes32_t{}, value2}}}}}},
            Code{});
        db.create_and_prune_block_history(block_number++);

        EXPECT_EQ(db.read_account(a), acct);
        EXPECT_EQ(db.read_storage(a, key1), value1);
        EXPECT_EQ(db.read_storage(a, key2), value2);

        if constexpr (std::same_as<TypeParam, RocksTrieDB>) {
            EXPECT_EQ(
                db.storage_root(a),
                0x3f9802e4f21fce3d2b07d21c8f2b60b22f7c745c455e752728030580177f8e11_bytes32);
            EXPECT_EQ(
                db.state_root(),
                0x3f7578fb3acc297f8847c7885717733b268cb52dc6b8e5a68aff31c254b6b5b3_bytes32);
        }

        EXPECT_EQ(db.starting_block_number, block_number - 1u);
    }

    {
        auto db = TypeParam{Writable{}, root, block_number, BLOCK_HISTORY};

        EXPECT_EQ(db.read_account(a), acct);
        EXPECT_EQ(db.read_storage(a, key1), value1);
        EXPECT_EQ(db.read_storage(a, key2), value2);

        if constexpr (std::same_as<TypeParam, RocksTrieDB>) {
            EXPECT_EQ(
                db.storage_root(a),
                0x3f9802e4f21fce3d2b07d21c8f2b60b22f7c745c455e752728030580177f8e11_bytes32);
            EXPECT_EQ(
                db.state_root(),
                0x3f7578fb3acc297f8847c7885717733b268cb52dc6b8e5a68aff31c254b6b5b3_bytes32);
        }

        db.commit(
            StateDeltas{
                {a,
                 StateDelta{
                     .account = {acct, acct},
                     .storage = {{key2, {value2, value1}}}}}},
            Code{});

        db.create_and_prune_block_history(block_number++);

        EXPECT_EQ(db.read_account(a), acct);
        EXPECT_EQ(db.read_storage(a, key1), value1);
        EXPECT_EQ(db.read_storage(a, key2), value1);

        if constexpr (std::same_as<TypeParam, RocksTrieDB>) {
            EXPECT_EQ(
                db.state_root(),
                0x0169f0b22c30d7d6f0bb7ea2a07be178e216b72f372a6a7bafe55602e5650e60_bytes32);
        }
        EXPECT_EQ(db.starting_block_number, block_number - 1u);
    }

    {
        auto db = TypeParam{Writable{}, root, block_number, BLOCK_HISTORY};
        EXPECT_EQ(db.read_account(a), acct);
        EXPECT_EQ(db.read_storage(a, key1), value1);
        EXPECT_EQ(db.read_storage(a, key2), value1);

        if constexpr (std::same_as<TypeParam, RocksTrieDB>) {
            EXPECT_EQ(
                db.state_root(),
                0x0169f0b22c30d7d6f0bb7ea2a07be178e216b72f372a6a7bafe55602e5650e60_bytes32);
        }
        EXPECT_EQ(db.starting_block_number, block_number);
    }

    {
        auto db = TypeParam{Writable{}, root, block_number - 1, BLOCK_HISTORY};

        EXPECT_EQ(db.read_account(a), acct);
        EXPECT_EQ(db.read_storage(a, key1), value1);
        EXPECT_EQ(db.read_storage(a, key2), value2);

        if constexpr (std::same_as<TypeParam, RocksTrieDB>) {
            EXPECT_EQ(
                db.storage_root(a),
                0x3f9802e4f21fce3d2b07d21c8f2b60b22f7c745c455e752728030580177f8e11_bytes32);
            EXPECT_EQ(
                db.state_root(),
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
        auto db = TypeParam{Writable{}, root, std::nullopt, BLOCK_HISTORY};

        Account acct{
            .balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};
        db.commit(
            StateDeltas{
                {a,
                 StateDelta{
                     .account = {std::nullopt, acct},
                     .storage =
                         {{key1, {bytes32_t{}, value1}},
                          {key2, {bytes32_t{}, value2}}}}}},
            Code{});

        db.create_and_prune_block_history(block_number++);

        EXPECT_EQ(db.read_account(a), acct);
        EXPECT_EQ(db.read_storage(a, key1), value1);
        EXPECT_EQ(db.read_storage(a, key2), value2);

        if constexpr (std::same_as<TypeParam, RocksTrieDB>) {
            EXPECT_EQ(
                db.storage_root(a),
                0x3f9802e4f21fce3d2b07d21c8f2b60b22f7c745c455e752728030580177f8e11_bytes32);
            EXPECT_EQ(
                db.state_root(),
                0x3f7578fb3acc297f8847c7885717733b268cb52dc6b8e5a68aff31c254b6b5b3_bytes32);
        }
        EXPECT_EQ(db.starting_block_number, block_number - 1u);
    }

    {
        auto db = TypeParam{Writable{}, root, std::nullopt, BLOCK_HISTORY};

        EXPECT_EQ(db.read_account(a), acct);
        EXPECT_EQ(db.read_storage(a, key1), value1);
        EXPECT_EQ(db.read_storage(a, key2), value2);

        if constexpr (std::same_as<TypeParam, RocksTrieDB>) {
            EXPECT_EQ(
                db.storage_root(a),
                0x3f9802e4f21fce3d2b07d21c8f2b60b22f7c745c455e752728030580177f8e11_bytes32);
            EXPECT_EQ(
                db.state_root(),
                0x3f7578fb3acc297f8847c7885717733b268cb52dc6b8e5a68aff31c254b6b5b3_bytes32);
        }

        db.commit(
            StateDeltas{
                {a,
                 StateDelta{
                     .account = {acct, acct},
                     .storage = {{key2, {value2, value1}}}}}},
            Code{});
        db.create_and_prune_block_history(block_number++);

        EXPECT_EQ(db.read_account(a), acct);
        EXPECT_EQ(db.read_storage(a, key1), value1);
        EXPECT_EQ(db.read_storage(a, key2), value1);

        if constexpr (std::same_as<TypeParam, RocksTrieDB>) {
            EXPECT_EQ(
                db.state_root(),
                0x0169f0b22c30d7d6f0bb7ea2a07be178e216b72f372a6a7bafe55602e5650e60_bytes32);
        }

        EXPECT_EQ(db.starting_block_number, block_number - 1u);
    }

    {
        auto db = TypeParam{Writable{}, root, std::nullopt, BLOCK_HISTORY};

        EXPECT_EQ(db.read_account(a), acct);
        EXPECT_EQ(db.read_storage(a, key1), value1);
        EXPECT_EQ(db.read_storage(a, key2), value1);

        if constexpr (std::same_as<TypeParam, RocksTrieDB>) {
            EXPECT_EQ(
                db.state_root(),
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
        auto db = TypeParam{Writable{}, root, block_number, BLOCK_HISTORY};
        Account acct{
            .balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};

        db.commit(
            StateDeltas{
                {a,
                 StateDelta{
                     .account = {std::nullopt, acct},
                     .storage =
                         {{key1, {bytes32_t{}, value1}},
                          {key2, {bytes32_t{}, value2}}}}}},
            Code{});

        db.create_and_prune_block_history(block_number++);

        db.create_and_prune_block_history(block_number++);
        db.create_and_prune_block_history(block_number++);

        EXPECT_EQ(db.read_account(a), acct);
        EXPECT_EQ(db.read_storage(a, key1), value1);
        EXPECT_EQ(db.read_storage(a, key2), value2);

        if constexpr (std::same_as<TypeParam, RocksTrieDB>) {
            EXPECT_EQ(
                db.storage_root(a),
                0x3f9802e4f21fce3d2b07d21c8f2b60b22f7c745c455e752728030580177f8e11_bytes32);
            EXPECT_EQ(
                db.state_root(),
                0x3f7578fb3acc297f8847c7885717733b268cb52dc6b8e5a68aff31c254b6b5b3_bytes32);
        }
    }

    {
        auto db = TypeParam{Writable{}, root, block_number, BLOCK_HISTORY};

        EXPECT_EQ(db.read_account(a), acct);
        EXPECT_EQ(db.read_storage(a, key1), value1);
        EXPECT_EQ(db.read_storage(a, key2), value2);

        if constexpr (std::same_as<TypeParam, RocksTrieDB>) {
            EXPECT_EQ(
                db.storage_root(a),
                0x3f9802e4f21fce3d2b07d21c8f2b60b22f7c745c455e752728030580177f8e11_bytes32);
            EXPECT_EQ(
                db.state_root(),
                0x3f7578fb3acc297f8847c7885717733b268cb52dc6b8e5a68aff31c254b6b5b3_bytes32);
        }
    }

    EXPECT_THROW(
        [&]() {
            auto const b = block_number - 1;
            try {
                auto const db = TypeParam(ReadOnly{}, root, b);
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

TYPED_TEST(RocksDBTest, read_only)
{
    auto const root = test::make_db_root(
        *testing::UnitTest::GetInstance()->current_test_info());
    Account const acct{
        .balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};

    {
        auto db = TypeParam{Writable{}, root, std::nullopt, 1};
        db.commit(
            StateDeltas{
                {a,
                 StateDelta{
                     .account = {std::nullopt, acct},
                     .storage =
                         {{key1, {bytes32_t{}, value1}},
                          {key2, {bytes32_t{}, value2}}}}}},
            Code{});
        db.create_and_prune_block_history(0);
    }

    {
        auto db = TypeParam{ReadOnly{}, root, 1};
        EXPECT_EQ(db.read_account(a), acct);
        EXPECT_EQ(db.read_storage(a, key1), value1);
        EXPECT_EQ(db.read_storage(a, key2), value2);

        if constexpr (std::same_as<TypeParam, RocksTrieDB>) {
            EXPECT_EQ(
                db.storage_root(a),
                0x3f9802e4f21fce3d2b07d21c8f2b60b22f7c745c455e752728030580177f8e11_bytes32);
            EXPECT_EQ(
                db.state_root(),
                0x3f7578fb3acc297f8847c7885717733b268cb52dc6b8e5a68aff31c254b6b5b3_bytes32);
        }
    }
}
