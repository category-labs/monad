#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp" // NOLINT

#include <monad/core/byte_string.hpp>
#include <monad/core/hex_literal.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/update.hpp>

#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

using namespace monad::mpt;
using namespace monad::literals;
using namespace monad::test;

TEST_F(InMemoryTrieGTest, find_error_message_test)
{
    auto const a = 0x000000deadbeef_hex;
    auto const b = 0x000001deadbeef_hex;
    auto const va = 0x1111_hex;
    auto const vb = 0x2222_hex;
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(a, va),
        make_update(b, vb));

    {
        auto [cursor, errc] = find_blocking(this->aux, NodeCursor{}, 0x00_hex);
        EXPECT_EQ(errc, DbError::root_node_is_null_failure);
    }

    {
        auto [cursor, errc] =
            find_blocking(this->aux, NodeCursor{*this->root}, 0x00_hex);
        EXPECT_EQ(errc, DbError::key_ends_earlier_than_node_failure);
    }

    {
        auto [cursor, errc] =
            find_blocking(this->aux, NodeCursor{*this->root}, 0x000000dead_hex);
        EXPECT_EQ(errc, DbError::key_ends_earlier_than_node_failure);
    }

    {
        auto [cursor, errc] =
            find_blocking(this->aux, NodeCursor{*this->root}, 0x000002_hex);
        EXPECT_EQ(errc, DbError::branch_not_exist_failure);
    }

    {
        auto [cursor, errc] = find_blocking(
            this->aux, NodeCursor{*this->root}, 0x000000deedbeaf_hex);
        EXPECT_EQ(errc, DbError::key_mismatch_failure);
    }

    {
        unsigned char const c = 0;
        Nibbles const find_key = concat(c, c, c, c, c);
        auto [cursor, errc] =
            find_blocking(this->aux, NodeCursor{*this->root}, find_key);
        EXPECT_EQ(errc, DbError::node_is_not_leaf_failure);
    }

    {
        auto [cursor, errc] =
            find_blocking(this->aux, NodeCursor{*this->root}, a);
        EXPECT_EQ(errc, DbError::success);
    }
}
