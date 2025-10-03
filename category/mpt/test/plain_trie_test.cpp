// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp" // NOLINT

#include <category/core/byte_string.hpp>
#include <category/core/hex_literal.hpp>
#include <category/mpt/detail/boost_fiber_workarounds.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/update.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <boost/fiber/future/future_status.hpp>

#include <chrono>
#include <utility>
#include <vector>

using namespace monad::mpt;
using namespace monad::literals;
using namespace monad::test;

template <typename TFixture>
struct PlainTrieTest : public TFixture
{
};

using PlainTrieTypes = ::testing::Types<InMemoryTrieGTest, OnDiskTrieGTest>;
TYPED_TEST_SUITE(PlainTrieTest, PlainTrieTypes);

namespace updates
{
    std::vector<std::pair<monad::byte_string, monad::byte_string>> const
        var_len_kv{
            {0x01111111_hex, 0xdead_hex}, // 0
            {0x11111111_hex, 0xbeef_hex}, // 1
            {0x11111111aaaa_hex, 0xdeafbeef_hex}, // 2
            {0x11111111aacd_hex, 0xabcd_hex}, // 3
            {0x111a1111_hex, 0xba_hex}, // 4
            {0x111b1111_hex, 0xbabe_hex}, // 5
            {0x111b1111aaaaaaaa_hex, 0xcafe_hex}, // 6
            {0x111b1111bbbbbbbb_hex, 0xbe_hex}, // 7
        };

    std::vector<std::pair<monad::byte_string, monad::byte_string>> const top_kv{
        {0x01111111_hex, 0xdead_hex}, // 0
        {0x11111111_hex, 0xbeef_hex}, // 1
        {0x111a1111_hex, 0xba_hex}, // 2
        {0x111b1111_hex, 0xbabe_hex}, // 3
    };

    std::vector<std::pair<monad::byte_string, monad::byte_string>> const
        nested_kv{
            {0xaaaa_hex, 0xdeafbeef_hex},
            {0xaacd_hex, 0xabcd_hex},
            {0xaaaaaaaa_hex, 0xcafe_hex},
            {0xbbbbbbbb_hex, 0xbe_hex},
        };
}

TYPED_TEST(PlainTrieTest, leaf_nodes_persist)
{
    UpdateList nested;
    auto const prefix = 0x00_hex;
    auto const key1 = 0x11_hex;
    auto const key2 = 0x22_hex;
    auto u1 = make_update(key1, monad::byte_string_view{});
    auto u2 = make_update(key2, monad::byte_string_view{});
    nested.push_front(u1);
    nested.push_front(u2);
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(prefix, {}, false, std::move(nested)));
    EXPECT_EQ(this->root->mask, 0b110);

    UpdateList nested2;
    auto e1 = make_erase(key1);
    nested2.push_front(e1);

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(prefix, {}, false, std::move(nested2)));
    EXPECT_EQ(this->root->mask, 0b100);
}

TYPED_TEST(PlainTrieTest, var_length_trie)
{
    // Variable-length tables support only a one-time insert; no deletions or
    // further updates are allowed.
    this->sm = std::make_unique<StateMachinePlainVarLen>();

    constexpr uint64_t version = 0;
    auto const &kv = updates::var_len_kv;
    // insert kv 0,1,2,3
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[0].first, kv[0].second),
        make_update(kv[1].first, kv[1].second),
        make_update(kv[2].first, kv[2].second),
        make_update(kv[3].first, kv[3].second),
        make_update(kv[4].first, kv[4].second),
        make_update(kv[5].first, kv[5].second),
        make_update(kv[6].first, kv[6].second),
        make_update(kv[7].first, kv[7].second));

    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[0].first, version)
            .first.node->value(),
        kv[0].second);
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[1].first, version)
            .first.node->value(),
        kv[1].second);
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[2].first, version)
            .first.node->value(),
        kv[2].second);
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[3].first, version)
            .first.node->value(),
        kv[3].second);

    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[0].first, version)
            .first.node->value(),
        kv[0].second);
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[1].first, version)
            .first.node->value(),
        kv[1].second);
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[2].first, version)
            .first.node->value(),
        kv[2].second);
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[3].first, version)
            .first.node->value(),
        kv[3].second);
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[4].first, version)
            .first.node->value(),
        kv[4].second);
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[5].first, version)
            .first.node->value(),
        kv[5].second);

    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[6].first, version)
            .first.node->value(),
        kv[6].second);
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[7].first, version)
            .first.node->value(),
        kv[7].second);

    EXPECT_EQ(this->root->mask, 0b11);
    EXPECT_FALSE(this->root->has_value());
    EXPECT_EQ(this->root->bitpacked.data_len, 0);
    EXPECT_EQ(this->root->path_nibbles_len(), 0);
    auto node0 = this->root->next(0);
    auto node1 = this->root->next(1); // 1111... 111a... 111b...
    EXPECT_EQ(node0->mask, 0);
    EXPECT_EQ(node1->mask, 1u << 1 | 1u << 0xa | 1u << 0xb);
    EXPECT_EQ(
        node0->path_nibble_view(), (NibblesView{1, 8, kv[0].first.data()}));
    EXPECT_EQ(node0->value(), kv[0].second);
    EXPECT_EQ(
        node1->path_nibble_view(), (NibblesView{1, 3, kv[1].first.data()}));

    auto node1111 = node1->next(0);
    auto node111a = node1->next(1);
    auto node111b = node1->next(2);
    EXPECT_EQ(node1111->value(), kv[1].second);
    EXPECT_EQ(node1111->mask, 1u << 0xa);
    auto node1111_aa = node1111->next(0);
    EXPECT_EQ(node1111_aa->mask, 1u << 0xa | 1u << 0xc);
    EXPECT_EQ(node1111_aa->next(0)->value(), kv[2].second);
    EXPECT_EQ(node1111_aa->next(1)->value(), kv[3].second);
    EXPECT_EQ(
        node111a->path_nibble_view(), (NibblesView{4, 8, kv[4].first.data()}));
    EXPECT_EQ(node111a->value(), kv[4].second);
    EXPECT_EQ(node111b->value(), kv[5].second);
    EXPECT_EQ(node111b->mask, 1u << 0xa | 1u << 0xb);
    EXPECT_EQ(
        node111b->next(node111b->to_child_index(0xa))->value(), kv[6].second);
    EXPECT_EQ(
        node111b->next(node111b->to_child_index(0xa))->path_nibble_view(),
        (NibblesView{9, 16, kv[6].first.data()}));
    EXPECT_EQ(
        node111b->next(node111b->to_child_index(0xb))->value(), kv[7].second);
    EXPECT_EQ(
        node111b->next(node111b->to_child_index(0xb))->path_nibble_view(),
        (NibblesView{9, 16, kv[7].first.data()}));
}

TYPED_TEST(PlainTrieTest, mismatch)
{
    constexpr uint64_t version = 0;
    std::vector<std::pair<monad::byte_string, monad::byte_string>> const kv{
        {0x12345678_hex, 0xdead_hex}, // 0
        {0x12346678_hex, 0xbeef_hex}, // 1
        {0x12445678_hex, 0xdeafbeef_hex}, // 2
        {0x12347678_hex, 0xba_hex}, // 3
        {0x123aabcd_hex, 0xbabe_hex}, // 4
    };

    /* insert 12345678, 12346678, 12445678
            12
          /    \
         34      445678
        / \
    5678  6678
    */
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[0].first, kv[0].second),
        make_update(kv[1].first, kv[1].second),
        make_update(kv[2].first, kv[2].second));
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[0].first, version)
            .first.node->value(),
        kv[0].second);
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[1].first, version)
            .first.node->value(),
        kv[1].second);
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[2].first, version)
            .first.node->value(),
        kv[2].second);

    EXPECT_EQ(this->root->mask, 0b11000);
    EXPECT_EQ(
        this->root->path_nibble_view(),
        (NibblesView{0, 2, kv[0].first.data()}));
    EXPECT_EQ(this->root->next(1)->value(), kv[2].second);
    auto left_leaf = this->root->next(0)->next(0);
    EXPECT_EQ(left_leaf->value(), kv[0].second);
    /* insert 12347678, 123aabcd
                  12
                /    \
              3       445678
             / \
            4   aabcd
          / | \
      5678 6678 7678
    */
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[3].first, kv[3].second),
        make_update(kv[4].first, kv[4].second));
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[1].first, version)
            .first.node->value(),
        kv[1].second);
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[2].first, version)
            .first.node->value(),
        kv[2].second);
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[3].first, version)
            .first.node->value(),
        kv[3].second);
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[4].first, version)
            .first.node->value(),
        kv[4].second);

    EXPECT_EQ(this->root->mask, 0b11000);
    EXPECT_EQ(
        this->root->path_nibble_view(),
        (NibblesView{0, 2, kv[0].first.data()}));
    auto node3 = this->root->next(0);
    EXPECT_EQ(node3->mask, 1u << 4 | 1u << 0xa);
    EXPECT_EQ(node3->bitpacked.data_len, 0);
    EXPECT_EQ(node3->path_bytes(), 0);
    auto node34 = node3->next(0);
    EXPECT_EQ(node34->mask, 0b11100000);
    EXPECT_EQ(node34->bitpacked.data_len, 0);
    EXPECT_EQ(node34->path_bytes(), 0);
    EXPECT_EQ(node34->next(0)->value_len, 2);
    EXPECT_EQ(node34->next(0)->value(), kv[0].second);
    EXPECT_EQ(node34->next(1)->value(), kv[1].second);
    EXPECT_EQ(node34->next(2)->value(), kv[3].second);
}

TYPED_TEST(PlainTrieTest, delete_wo_incarnation)
{
    auto const &kv = updates::top_kv;
    auto const &nested_kv = updates::nested_kv;

    UpdateList nested1;
    Update u1 = make_update(nested_kv[0].first, nested_kv[0].second);
    Update u2 = make_update(nested_kv[1].first, nested_kv[1].second);
    nested1.push_front(u1);
    nested1.push_front(u2);

    UpdateList nested2;
    Update u3 = make_update(nested_kv[2].first, nested_kv[2].second);
    Update u4 = make_update(nested_kv[3].first, nested_kv[3].second);
    nested2.push_front(u3);
    nested2.push_front(u4);

    // insert all
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[0].first, kv[0].second),
        make_update(kv[1].first, kv[1].second, false, std::move(nested1)),
        make_update(kv[2].first, kv[2].second),
        make_update(kv[3].first, kv[3].second, false, std::move(nested2)));
    // erase kv0
    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_erase(kv[0].first));
    EXPECT_EQ(this->root->mask, 2 | 1u << 0xa | 1u << 0xb);
    EXPECT_EQ(
        this->root->path_nibble_view(),
        (NibblesView{0, 3, kv[1].first.data()}));

    // erase kv3, so as its subtrie
    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_erase(kv[3].first));
    EXPECT_EQ(this->root->mask, 2 | 1u << 0xa);
    EXPECT_EQ(
        this->root->path_nibble_view(),
        (NibblesView{0, 3, kv[1].first.data()}));

    // erase kv1, so as its subtrie
    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_erase(kv[1].first));
    // only kv2 left
    EXPECT_EQ(this->root->mask, 0);
    EXPECT_EQ(this->root->value(), kv[2].second);
    EXPECT_EQ(
        this->root->path_nibble_view(),
        (NibblesView{0, 8, kv[2].first.data()}));
}

TYPED_TEST(PlainTrieTest, delete_with_incarnation)
{
    constexpr uint64_t version = 0;
    // upsert a bunch of var lengths kv
    auto const &kv = updates::top_kv;
    auto const &nested_kv = updates::nested_kv;

    {
        UpdateList nested;
        Update u = make_update(nested_kv[0].first, nested_kv[0].second);
        nested.push_front(u);
        this->root = upsert_updates(
            this->aux,
            *this->sm,
            std::move(this->root),
            make_update(kv[0].first, kv[0].second), // 0x01111111
            make_update( // 0x11111111 -> 0xaaaa
                kv[1].first,
                kv[1].second,
                false,
                std::move(nested)));
    }
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[0].first, version)
            .first.node->value(),
        kv[0].second);
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[1].first, version)
            .first.node->value(),
        kv[1].second);
    EXPECT_EQ(
        find_blocking(
            this->aux, this->root, kv[1].first + nested_kv[0].first, version)
            .first.node->value(),
        nested_kv[0].second);

    {
        UpdateList nested;
        Update u = make_update(nested_kv[1].first, nested_kv[1].second);
        nested.push_front(u);
        // upsert kv[1] with incarnation and new nested key
        this->root = upsert_updates( // 0x11111111 -> 0xaacd
            this->aux,
            *this->sm,
            std::move(this->root),
            make_update(kv[1].first, kv[1].second, true, std::move(nested)));
    }
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[0].first, version)
            .first.node->value(),
        kv[0].second);
    EXPECT_EQ(
        find_blocking(this->aux, this->root, kv[1].first, version)
            .first.node->value(),
        kv[1].second);
    EXPECT_EQ(
        find_blocking(
            this->aux, this->root, kv[1].first + nested_kv[1].first, version)
            .first.node->value(),
        nested_kv[1].second);
    EXPECT_EQ(
        find_blocking(
            this->aux, this->root, kv[1].first + nested_kv[0].first, version)
            .second,
        find_result::key_mismatch_failure);
}

TYPED_TEST(PlainTrieTest, large_values)
{
    constexpr uint64_t version = 0;
    // make sure leaves are not cached
    auto const key1 = 0x0000112_hex;
    auto const key2 = 0x0000123_hex;
    auto const value1 = monad::byte_string(100 * 1024 * 1024, 0xf); // 100 MB
    auto const value2 = monad::byte_string(255 * 1024 * 1024, 0x3); // 255 MB

    auto same_upsert_to_clear_nodes_outside_cache_level = [&] {
        this->root = upsert_updates(
            this->aux,
            *this->sm,
            std::move(this->root),
            make_update(key1, value1),
            make_update(key2, value2));
    };

    same_upsert_to_clear_nodes_outside_cache_level();
    {
        auto [leaf_it, res] =
            find_blocking(this->aux, this->root, key1, version);
        auto &leaf = leaf_it.node;
        EXPECT_EQ(res, find_result::success);
        EXPECT_NE(leaf, nullptr);
        EXPECT_TRUE(leaf->has_value());
        EXPECT_EQ(leaf->value(), value1);
    }

    same_upsert_to_clear_nodes_outside_cache_level();
    {
        auto [leaf_it, res] =
            find_blocking(this->aux, this->root, key2, version);
        auto &leaf = leaf_it.node;
        EXPECT_EQ(res, find_result::success);
        EXPECT_NE(leaf, nullptr);
        EXPECT_TRUE(leaf->has_value());
        EXPECT_EQ(leaf->value(), value2);
    }

    same_upsert_to_clear_nodes_outside_cache_level();
    {
        monad::threadsafe_boost_fibers_promise<find_cursor_result_type> p;
        auto fut = p.get_future();
        inflight_map_t inflights;
        find_notify_fiber_future(this->aux, inflights, p, this->root, key1);
        while (fut.wait_for(std::chrono::seconds(0)) !=
               ::boost::fibers::future_status::ready) {
            this->aux.io->wait_until_done();
        }
        auto [leaf_it, res] = fut.get();
        auto &leaf = leaf_it.node;
        EXPECT_EQ(res, find_result::success);
        EXPECT_NE(leaf, nullptr);
        EXPECT_TRUE(leaf->has_value());
        EXPECT_EQ(leaf->value(), value1);
    }

    same_upsert_to_clear_nodes_outside_cache_level();
    {
        monad::threadsafe_boost_fibers_promise<find_cursor_result_type> p;
        auto fut = p.get_future();
        inflight_map_t inflights;
        find_notify_fiber_future(this->aux, inflights, p, this->root, key2);
        while (fut.wait_for(std::chrono::seconds(0)) !=
               ::boost::fibers::future_status::ready) {
            this->aux.io->wait_until_done();
        }
        auto [leaf_it, res] = fut.get();
        auto &leaf = leaf_it.node;
        EXPECT_EQ(res, find_result::success);
        EXPECT_NE(leaf, nullptr);
        EXPECT_TRUE(leaf->has_value());
        EXPECT_EQ(leaf->value(), value2);
    }

    same_upsert_to_clear_nodes_outside_cache_level();
}

TYPED_TEST(PlainTrieTest, multi_level_find_blocking)
{
    constexpr unsigned prefix_len = 6;
    using TestStateMachine = StateMachineAlways<
        EmptyCompute,
        StateMachineConfig{.variable_length_start_depth = prefix_len}>;

    this->sm = std::make_unique<TestStateMachine>();
    constexpr uint64_t version = 0;
    // upsert a bunch of var lengths kv
    auto const &kv = updates::var_len_kv;
    // always insert the same updates to the second level trie
    Update u1 = make_update(kv[0].first, kv[0].second); // 0x01111111
    Update u2 = make_update(kv[1].first, kv[1].second); // 0x11111111
    Update u3 = make_update(kv[2].first, kv[2].second); // 0x11111111aaaa

    auto upsert_and_find_with_prefix = [&](monad::byte_string const prefix,
                                           monad::byte_string const top_value) {
        MONAD_ASSERT(NibblesView{prefix}.nibble_size() == prefix_len);
        UpdateList updates;
        updates.push_front(u1);
        updates.push_front(u2);
        updates.push_front(u3);
        // insert
        this->root = upsert_updates(
            this->aux,
            *this->sm,
            std::move(this->root),
            make_update(prefix, top_value, false, std::move(updates)));
        // find blocking on multi-level trie
        auto [begin, errc] =
            find_blocking(this->aux, this->root, prefix, version);
        EXPECT_EQ(errc, find_result::success);
        EXPECT_EQ(begin.node->number_of_children(), 2);
        EXPECT_EQ(begin.node->value(), top_value);

        EXPECT_EQ(
            find_blocking(this->aux, begin, kv[0].first, version)
                .first.node->value(),
            kv[0].second);
        EXPECT_EQ(
            find_blocking(this->aux, begin, kv[1].first, version)
                .first.node->value(),
            kv[1].second);
        EXPECT_EQ(
            find_blocking(this->aux, begin, kv[2].first, version)
                .first.node->value(),
            kv[2].second);
    };

    upsert_and_find_with_prefix(0x000001_hex, 0xdeadbeef_hex);
    upsert_and_find_with_prefix(0x000002_hex, 0x0123456789_hex);
    upsert_and_find_with_prefix(0x000003_hex, 0x9876543210_hex);
    upsert_and_find_with_prefix(0x000004_hex, 0xdeadbeef_hex);
}

TYPED_TEST(PlainTrieTest, node_version)
{
    // Verify node verisons after multiple upserts
    std::vector<monad::byte_string> const keys = {
        0x000000_hex, 0x000001_hex, 0x000002_hex, 0x000010_hex, 0x000011_hex};
    auto const value = 0xdeadbeaf_hex;

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(keys[0], value, false, {}, 0));
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(keys[1], value, false, {}, 1));
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(keys[2], value, false, {}, 2));

    EXPECT_EQ(this->root->version, 2);

    auto read_child = [&](Node &parent,
                          unsigned const index) -> Node::UniquePtr {
        return read_node_blocking(this->aux, parent.fnext(index), 0);
    };
    if (this->root->next(0)) {
        EXPECT_EQ(this->root->next(0)->version, 0);
    }
    else {
        EXPECT_EQ(read_child(*this->root, 0)->version, 0);
    }

    if (this->root->next(1)) {
        EXPECT_EQ(this->root->next(1)->version, 1);
    }
    else {
        EXPECT_EQ(read_child(*this->root, 1)->version, 1);
    }

    if (this->root->next(2)) {
        EXPECT_EQ(this->root->next(2)->version, 2);
    }
    else {
        EXPECT_EQ(read_child(*this->root, 2)->version, 2);
    }

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(keys[3], value, false, {}, 3));
    EXPECT_EQ(this->root->version, 3);
    if (this->root->next(0)) {
        EXPECT_EQ(this->root->next(0)->version, 2);
    }
    else {
        EXPECT_EQ(read_child(*this->root, 0)->version, 2);
    }
    if (this->root->next(1)) {
        EXPECT_EQ(this->root->next(1)->version, 3);
    }
    else {
        EXPECT_EQ(read_child(*this->root, 1)->version, 3);
    }

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(keys[4], value, false, {}, 4));
    EXPECT_EQ(this->root->version, 4);
    if (this->root->next(0)) {
        EXPECT_EQ(this->root->next(0)->version, 2);
    }
    else {
        EXPECT_EQ(read_child(*this->root, 0)->version, 2);
    }

    if (!this->root->next(1)) {
        this->root->set_next(1, read_child(*this->root, 1));
    }
    EXPECT_EQ(this->root->next(1)->version, 4);

    if (this->root->next(1)->next(0)) {
        EXPECT_EQ(this->root->next(1)->next(0)->version, 3);
    }
    else {
        EXPECT_EQ(read_child(*this->root->next(1), 0)->version, 3);
    }

    // erase should not update the version of interior nodes
    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_erase(keys[4]));
    EXPECT_EQ(this->root->version, 4);
    EXPECT_NE(this->root->next(1), nullptr);
    EXPECT_EQ(this->root->next(1)->version, 4);
    EXPECT_NE(this->root->next(0), nullptr);
    EXPECT_EQ(this->root->next(0)->version, 2);
}
