#include <monad/core/account.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/in_memory_trie_db.hpp>
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

using DBTypes = ::testing::Types<InMemoryTrieDB>;
TYPED_TEST_SUITE(DBTest, DBTypes);

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

TYPED_TEST(DBTest, ModifyStorageOfAccount)
{
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
    auto db = test::make_db<TypeParam>();
    db.commit(
        StateDeltas{{a, StateDelta{.account = {std::nullopt, std::nullopt}}}},
        Code{});

    EXPECT_EQ(db.read_account(a), std::nullopt);
    EXPECT_EQ(db.state_root(), NULL_ROOT);
}

TYPED_TEST(DBTest, delete_account_modify_storage_regression)
{
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

TYPED_TEST(DBTest, storage_deletion)
{
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
                 .storage = {{key1, {value1, bytes32_t{}}}}}}},
        Code{});

    EXPECT_EQ(
        db.state_root(),
        0xcc04b7a59a7c5d1f294402a0cbe42b5102db928fb2fad9d0d6f8c2a21a34c195_bytes32);
}
