#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>

#include <monad/db/in_memory_trie_db.hpp>
#include <monad/db/rocks_trie_db.hpp>

#include <monad/state/code_state.hpp>
#include <monad/state/state_changes.hpp>

#include <monad/test/make_db.hpp>

#include <gtest/gtest.h>

#include <unordered_map>

using namespace monad;
using namespace monad::state;

static constexpr auto a = 0x5353535353535353535353535353535353535353_address;
static constexpr auto b = 0xbebebebebebebebebebebebebebebebebebebebe_address;
static constexpr auto code_hash1 =
    0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
static constexpr auto code_hash2 =
    0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
static constexpr auto code_hash3 =
    0x5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b_bytes32;
static constexpr auto code1 =
    byte_string{0x65, 0x74, 0x68, 0x65, 0x72, 0x6d, 0x69};
static constexpr auto code2 =
    byte_string{0x6e, 0x65, 0x20, 0x2d, 0x20, 0x45, 0x55, 0x31, 0x34};
static constexpr auto code3 =
    byte_string{0x6e, 0x63, 0x40, 0x2d, 0x20, 0x45, 0x55, 0x31, 0x33};

template <typename TDB>
struct CodeStateTest : public testing::Test
{
};
using DBTypes = ::testing::Types<db::InMemoryTrieDB, db::RocksTrieDB>;
TYPED_TEST_SUITE(CodeStateTest, DBTypes);

TYPED_TEST(CodeStateTest, code_at)
{
    auto db = test::make_db<TypeParam>();

    Account acct{.code_hash = code_hash1};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct}},
        .storage_changes = {},
        .code_changes = {{code_hash1, code1}}});
    CodeState s{db};

    EXPECT_EQ(code1, s.code_at(code_hash1));
}

TYPED_TEST(CodeStateTest, changeset_code_at)
{
    auto db = test::make_db<TypeParam>();
    Account acct{.code_hash = code_hash1};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct}},
        .storage_changes = {},
        .code_changes = {{code_hash1, code1}}});
    CodeState s{db};

    typename decltype(s)::ChangeSet changeset{s};
    EXPECT_EQ(code1, changeset.code_at(code_hash1));
}

TYPED_TEST(CodeStateTest, set_code)
{
    auto db = test::make_db<TypeParam>();
    Account acct{.code_hash = code_hash1};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct}},
        .storage_changes = {},
        .code_changes = {{code_hash1, code1}}});
    CodeState s{db};

    typename decltype(s)::ChangeSet changeset{s};
    changeset.set_code(code_hash2, code2);
    changeset.set_code(code_hash3, byte_string{});

    EXPECT_EQ(changeset.code_at(code_hash1), code1);
    EXPECT_EQ(changeset.code_at(code_hash2), code2);
    EXPECT_EQ(changeset.code_at(code_hash3), byte_string{});
}

TYPED_TEST(CodeStateTest, get_code_size)
{
    auto db = test::make_db<TypeParam>();
    Account acct{.code_hash = code_hash1};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct}},
        .storage_changes = {},
        .code_changes = {{code_hash1, code1}}});
    CodeState s{db};

    typename decltype(s)::ChangeSet changeset{s};

    EXPECT_EQ(changeset.get_code_size(code_hash1), code1.size());
}

TYPED_TEST(CodeStateTest, copy_code)
{
    auto db = test::make_db<TypeParam>();
    Account acct_a{.code_hash = code_hash1};
    Account acct_b{.code_hash = code_hash2};

    db.commit(state::StateChanges{
        .account_changes = {{a, acct_a}, {b, acct_b}},
        .storage_changes = {},
        .code_changes = {{code_hash1, code1}, {code_hash2, code2}}});
    CodeState s{db};

    static constexpr unsigned size{8};
    uint8_t buffer[size];

    typename decltype(s)::ChangeSet changeset{s};

    { // underflow
        auto const total = changeset.copy_code(code_hash1, 0u, buffer, size);
        EXPECT_EQ(total, code1.size());
        EXPECT_EQ(0, std::memcmp(buffer, code1.c_str(), total));
    }
    { // offset
        static constexpr auto offset = 2u;
        static constexpr auto to_copy = 3u;
        auto const offset_total =
            changeset.copy_code(code_hash1, offset, buffer, to_copy);
        EXPECT_EQ(offset_total, to_copy);
        EXPECT_EQ(0, std::memcmp(buffer, code1.c_str() + offset, offset_total));
    }
    { // offset overflow
        static constexpr auto offset = 4u;
        auto const offset_total =
            changeset.copy_code(code_hash1, offset, buffer, size);
        EXPECT_EQ(offset_total, 3u);
        EXPECT_EQ(0, std::memcmp(buffer, code1.c_str() + offset, offset_total));
    }
    { // regular overflow
        auto const total = changeset.copy_code(code_hash2, 0u, buffer, size);
        EXPECT_EQ(total, size);
        EXPECT_EQ(0, std::memcmp(buffer, code2.c_str(), total));
    }
    { // null hash
        auto const total = changeset.copy_code(NULL_HASH, 1u, buffer, size);
        EXPECT_EQ(total, 0);
    }
}

TYPED_TEST(CodeStateTest, merge_changes)
{
    auto db = test::make_db<TypeParam>();
    Account acct{.code_hash = code_hash1};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct}},
        .storage_changes = {},
        .code_changes = {{code_hash1, code1}}});
    CodeState s{db};

    {
        typename decltype(s)::ChangeSet changeset{s};
        changeset.set_code(code_hash2, code2);
        EXPECT_TRUE(s.can_merge(changeset));
        s.merge_changes(changeset);
    }
    EXPECT_EQ(s.code_at(code_hash2), code2);

    {
        typename decltype(s)::ChangeSet changeset{s};
        changeset.set_code(code_hash1, code3);
        EXPECT_FALSE(s.can_merge(changeset));
    }
}

TYPED_TEST(CodeStateTest, can_merge_after_set_same_code)
{
    auto db = test::make_db<TypeParam>();
    Account acct{.code_hash = code_hash1};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct}},
        .storage_changes = {},
        .code_changes = {{code_hash1, code1}}});
    CodeState s{db};

    typename decltype(s)::ChangeSet changeset{s};
    changeset.set_code(code_hash1, code1);
    EXPECT_TRUE(s.can_merge(changeset));
    s.merge_changes(changeset);
}

TYPED_TEST(CodeStateTest, revert)
{
    auto db = test::make_db<TypeParam>();
    Account acct{.code_hash = code_hash1};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct}},
        .storage_changes = {},
        .code_changes = {{code_hash1, code1}}});
    CodeState s{db};

    {
        typename decltype(s)::ChangeSet changeset{s};
        changeset.set_code(code_hash2, code2);
        EXPECT_TRUE(s.can_merge(changeset));
        changeset.revert();
        s.merge_changes(changeset);
    }
    EXPECT_EQ(0, s.code_at(code_hash2).size());
}

TYPED_TEST(CodeStateTest, cant_merge_colliding_merge)
{
    auto db = test::make_db<TypeParam>();
    CodeState s{db};

    {
        typename decltype(s)::ChangeSet changeset{s};
        changeset.set_code(code_hash1, code1);
        EXPECT_TRUE(s.can_merge(changeset));
        s.merge_changes(changeset);
    }
    {
        typename decltype(s)::ChangeSet changeset{s};
        changeset.set_code(code_hash1, code2);
        EXPECT_FALSE(s.can_merge(changeset));
    }
}

TYPED_TEST(CodeStateTest, cant_merge_colliding_store)
{
    auto db = test::make_db<TypeParam>();
    Account acct{.code_hash = code_hash1};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct}},
        .storage_changes = {},
        .code_changes = {{code_hash1, code1}}});
    CodeState s{db};

    typename decltype(s)::ChangeSet changeset{s};
    changeset.set_code(code_hash1, code2);
    EXPECT_FALSE(s.can_merge(changeset));
}

TYPED_TEST(CodeStateTest, merge_multiple_changes)
{
    auto db = test::make_db<TypeParam>();
    CodeState s{db};

    {
        typename decltype(s)::ChangeSet changeset{s};
        changeset.set_code(code_hash1, code1);
        EXPECT_TRUE(s.can_merge(changeset));
        s.merge_changes(changeset);
    }
    {
        typename decltype(s)::ChangeSet changeset{s};
        changeset.set_code(code_hash2, code2);
        EXPECT_TRUE(s.can_merge(changeset));
        s.merge_changes(changeset);
    }
    EXPECT_EQ(s.code_at(code_hash1), code1);
    EXPECT_EQ(s.code_at(code_hash2), code2);
}

TYPED_TEST(CodeStateTest, can_commit)
{
    auto db = test::make_db<TypeParam>();
    Account acct{.code_hash = code_hash3};
    db.commit(state::StateChanges{
        .account_changes = {{a, acct}},
        .storage_changes = {},
        .code_changes = {{code_hash3, code3}}});
    CodeState s{db};

    {
        typename decltype(s)::ChangeSet changeset{s};
        changeset.set_code(code_hash1, code1);
        changeset.set_code(code_hash2, code2);
        EXPECT_TRUE(s.can_merge(changeset));
        s.merge_changes(changeset);
    }
    EXPECT_TRUE(s.can_commit());
}

TYPED_TEST(CodeStateTest, can_commit_multiple)
{
    auto db = test::make_db<TypeParam>();
    CodeState s{db};

    {
        typename decltype(s)::ChangeSet changeset{s};
        changeset.set_code(code_hash1, code1);
        changeset.set_code(code_hash2, code2);
        EXPECT_TRUE(s.can_merge(changeset));
        s.merge_changes(changeset);
    }

    EXPECT_TRUE(s.can_commit());

    {
        typename decltype(s)::ChangeSet changeset{s};
        changeset.set_code(code_hash3, code3);
        EXPECT_TRUE(s.can_merge(changeset));
        s.merge_changes(changeset);
    }
    EXPECT_TRUE(s.can_commit());
}

TYPED_TEST(CodeStateTest, distinct_account_identical_code)
{
    auto db = test::make_db<TypeParam>();
    CodeState s{db};

    typename decltype(s)::ChangeSet changeset{s};
    changeset.set_code(code_hash1, code1);
    changeset.set_code(code_hash1, code1);
    EXPECT_TRUE(s.can_merge(changeset));
    s.merge_changes(changeset);
}
