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

TEST_F(OnDiskTrieGTest, find_blocking_continuation)
{
    // state machine cache the nodes whose path <= 6 nibbles
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

    EXPECT_EQ(this->root->mask, 0b011);

    // find_blocking in memory
    auto [cursor, end_nibble, errc] =
        find_blocking(this->aux, NodeCursor{*this->root}, NibblesView{a}, true);
    EXPECT_EQ(errc, find_result_msg::need_to_read_from_disk);
    EXPECT_EQ(end_nibble, 5);

    // find continuation from on disk
    auto next_key = NibblesView{a}.substr(end_nibble);
    auto [cursor2, end_nibble2, errc2] =
        find_blocking(this->aux, cursor, next_key);
    EXPECT_EQ(errc2, find_result_msg::success);
    EXPECT_EQ(end_nibble2, next_key.nibble_size());
    EXPECT_EQ(end_nibble + end_nibble2, NibblesView{a}.nibble_size());
    EXPECT_EQ(cursor2.node->value(), va);
}

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
        auto [cursor, end_nibble, errc] =
            find_blocking(this->aux, NodeCursor{}, 0x00_hex);
        EXPECT_EQ(errc, find_result_msg::root_node_is_null_failure);
        EXPECT_EQ(end_nibble, 0);
    }

    {
        auto [cursor, end_nibble, errc] =
            find_blocking(this->aux, NodeCursor{*this->root}, 0x00_hex);
        EXPECT_EQ(errc, find_result_msg::key_ends_earlier_than_node_failure);
        EXPECT_EQ(end_nibble, 2);
    }

    {
        auto [cursor, end_nibble, errc] =
            find_blocking(this->aux, NodeCursor{*this->root}, 0x000000dead_hex);
        EXPECT_EQ(errc, find_result_msg::key_ends_earlier_than_node_failure);
        EXPECT_EQ(end_nibble, 10);
    }

    {
        auto [cursor, end_nibble, errc] =
            find_blocking(this->aux, NodeCursor{*this->root}, 0x000002_hex);
        EXPECT_EQ(errc, find_result_msg::branch_not_exist_failure);
        EXPECT_EQ(end_nibble, 5);
    }

    {
        auto [cursor, end_nibble, errc] = find_blocking(
            this->aux, NodeCursor{*this->root}, 0x000000deedbeaf_hex);
        EXPECT_EQ(errc, find_result_msg::key_mismatch_failure);
        EXPECT_EQ(end_nibble, 8);
    }

    {
        unsigned char const c = 0;
        Nibbles const find_key = concat(c, c, c, c, c);
        auto [cursor, end_nibble, errc] =
            find_blocking(this->aux, NodeCursor{*this->root}, find_key);
        EXPECT_EQ(errc, find_result_msg::node_is_not_leaf_failure);
        EXPECT_EQ(end_nibble, 5);
    }

    {
        auto [cursor, end_nibble, errc] =
            find_blocking(this->aux, NodeCursor{*this->root}, a);
        EXPECT_EQ(errc, find_result_msg::success);
        EXPECT_EQ(end_nibble, 14);
    }
}
