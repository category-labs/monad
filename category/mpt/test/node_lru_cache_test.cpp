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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/node_cache.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <memory>
#include <utility>

using namespace monad::mpt;
using namespace monad::literals;

TEST(NodeCache, works)
{
    NodeCache node_cache(3 * NodeCache::AVERAGE_NODE_SIZE);
    NodeCache::ConstAccessor acc;

    auto make_node = [&](uint32_t v) {
        monad::byte_string value(84, 0);
        memcpy(value.data(), &v, 4);
        std::shared_ptr<Node> node =
            monad::mpt::make_node(0, {}, {}, std::move(value), 0, 0);
        MONAD_ASSERT(node->get_mem_size() == NodeCache::AVERAGE_NODE_SIZE);
        return node;
    };
    auto get_acc_value = [&] -> uint32_t {
        auto const view(acc->second->val.first->value());
        MONAD_ASSERT(84 == view.size());
        return *(uint32_t const *)view.data();
    };
    node_cache.insert(virtual_chunk_offset_t(1, 0, 1), make_node(0x123));
    node_cache.insert(virtual_chunk_offset_t(2, 0, 1), make_node(0xdead));
    node_cache.insert(virtual_chunk_offset_t(3, 0, 1), make_node(0xbeef));
    EXPECT_EQ(node_cache.size(), 3);

    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(3, 0, 1)));
    EXPECT_EQ(get_acc_value(), 0xbeef);
    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(2, 0, 1)));
    EXPECT_EQ(get_acc_value(), 0xdead);
    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(1, 0, 1)));
    EXPECT_EQ(get_acc_value(), 0x123);

    node_cache.insert(virtual_chunk_offset_t(4, 0, 1), make_node(0xcafe));
    EXPECT_EQ(node_cache.size(), 3);

    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(2, 0, 1)));
    EXPECT_EQ(get_acc_value(), 0xdead);
    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(1, 0, 1)));
    EXPECT_EQ(get_acc_value(), 0x123);
    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(4, 0, 1)));
    EXPECT_EQ(get_acc_value(), 0xcafe);

    node_cache.insert(virtual_chunk_offset_t(2, 0, 1), make_node(0xc0ffee));
    node_cache.insert(virtual_chunk_offset_t(5, 0, 1), make_node(100));
    EXPECT_EQ(node_cache.size(), 3);

    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(2, 0, 1)));
    EXPECT_EQ(get_acc_value(), 0xc0ffee);
    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(4, 0, 1)));
    EXPECT_EQ(get_acc_value(), 0xcafe);
    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(5, 0, 1)));
    EXPECT_EQ(get_acc_value(), 100);

    monad::byte_string large_value(84 * 3, 0);
    memcpy(large_value.data(), "hihi", 4);
    auto const node =
        monad::mpt::make_node(0, {}, {}, std::move(large_value), 0, 0);
    EXPECT_EQ(node->get_mem_size(), 272);
    node_cache.insert(virtual_chunk_offset_t(6, 0, 1), node);
    // Everything else should get evicted
    EXPECT_EQ(node_cache.size(), 1);
    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(6, 0, 1)));
    auto const view(acc->second->val.first->value());
    EXPECT_EQ(0, memcmp(view.data(), "hihi", 4));

    // re-insert
    node_cache.insert(virtual_chunk_offset_t(1, 0, 1), make_node(0x123));
    EXPECT_EQ(node_cache.size(), 1);
    node_cache.insert(virtual_chunk_offset_t(1, 0, 0), make_node(0xdead));
    EXPECT_EQ(node_cache.size(), 2);
    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(1, 0, 1)));
    EXPECT_EQ(get_acc_value(), 0x123);
    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(1, 0, 0)));
    EXPECT_EQ(get_acc_value(), 0xdead);
}

// Value bytes chosen so get_mem_size() lands on a multiple of
// AVERAGE_NODE_SIZE: 84 gives exactly one, 84*3 exactly 272. Parameterizing
// this matters -- nodes of exactly AVERAGE_NODE_SIZE make the slot bound and
// the byte bound fall on the same insert, which hides the byte bound.
namespace
{
    std::shared_ptr<Node> make_node(size_t const value_bytes = 84)
    {
        monad::byte_string value(value_bytes, 0);
        return monad::mpt::make_node(0, {}, {}, std::move(value), 0, 0);
    }

    constexpr size_t LARGE_VALUE_BYTES = 84 * 3; // 272-byte node
}

TEST(NodeCache, counts_hits_misses_and_evictions)
{
    NodeCache node_cache(2 * NodeCache::AVERAGE_NODE_SIZE);
    NodeCache::ConstAccessor acc;

    EXPECT_FALSE(node_cache.find(acc, virtual_chunk_offset_t(1, 0, 1)));
    node_cache.insert(virtual_chunk_offset_t(1, 0, 1), make_node());
    node_cache.insert(virtual_chunk_offset_t(2, 0, 1), make_node());
    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(1, 0, 1)));
    EXPECT_EQ(node_cache.stats().evictions, 0u);

    // Capacity is two slots, so the third key reuses the LRU tail.
    node_cache.insert(virtual_chunk_offset_t(3, 0, 1), make_node());

    auto const stats = node_cache.stats();
    EXPECT_EQ(stats.hits, 1u);
    EXPECT_EQ(stats.misses, 1u);
    EXPECT_EQ(stats.evictions, 1u);
}

// The byte bound, which is NodeCache's own and is reached only when nodes run
// larger than AVERAGE_NODE_SIZE. Eight slots, but the budget only pays for
// three of these nodes.
TEST(NodeCache, evicts_on_the_byte_bound_with_slots_to_spare)
{
    NodeCache node_cache(8 * NodeCache::AVERAGE_NODE_SIZE);
    auto const node_bytes = make_node(LARGE_VALUE_BYTES)->get_mem_size();
    ASSERT_GT(node_bytes, NodeCache::AVERAGE_NODE_SIZE);
    ASSERT_LT(3 * node_bytes, node_cache.max_bytes());
    ASSERT_GT(4 * node_bytes, node_cache.max_bytes());

    for (uint32_t i = 1; i <= 3; ++i) {
        node_cache.insert(
            virtual_chunk_offset_t(i, 0, 1), make_node(LARGE_VALUE_BYTES));
    }
    ASSERT_EQ(node_cache.size(), 3);
    ASSERT_EQ(node_cache.stats().evictions, 0u);

    node_cache.insert(
        virtual_chunk_offset_t(4, 0, 1), make_node(LARGE_VALUE_BYTES));

    EXPECT_EQ(node_cache.stats().evictions, 1u);
    EXPECT_EQ(node_cache.size(), 3);
    EXPECT_EQ(node_cache.used_bytes(), 3 * node_bytes);
    EXPECT_LE(node_cache.used_bytes(), node_cache.max_bytes());
    // The tail went, not some other key.
    EXPECT_FALSE(node_cache.contains(virtual_chunk_offset_t(1, 0, 1)));
    EXPECT_TRUE(node_cache.contains(virtual_chunk_offset_t(4, 0, 1)));
}

// Overwriting a key replaces an entry already counted against the budget, so
// it must not evict anything to make room it does not need.
TEST(NodeCache, overwriting_a_key_does_not_evict_to_make_room)
{
    NodeCache node_cache(2 * NodeCache::AVERAGE_NODE_SIZE);
    NodeCache::ConstAccessor acc;

    node_cache.insert(virtual_chunk_offset_t(1, 0, 1), make_node());
    node_cache.insert(virtual_chunk_offset_t(2, 0, 1), make_node());
    auto const full = node_cache.used_bytes();
    ASSERT_EQ(node_cache.size(), 2);
    ASSERT_EQ(node_cache.stats().evictions, 0u);

    node_cache.insert(virtual_chunk_offset_t(1, 0, 1), make_node());

    EXPECT_EQ(node_cache.used_bytes(), full);
    EXPECT_EQ(node_cache.size(), 2);
    EXPECT_EQ(node_cache.stats().evictions, 0u);
    EXPECT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(2, 0, 1)));
}

// A same-size overwrite cannot tell the net charge apart from charging the
// full incoming size and subtracting it again, so vary the size both ways.
TEST(NodeCache, overwriting_a_key_charges_the_size_difference)
{
    NodeCache node_cache(8 * NodeCache::AVERAGE_NODE_SIZE);
    auto const small = make_node()->get_mem_size();
    auto const large = make_node(LARGE_VALUE_BYTES)->get_mem_size();

    node_cache.insert(virtual_chunk_offset_t(1, 0, 1), make_node());
    node_cache.insert(virtual_chunk_offset_t(2, 0, 1), make_node());
    ASSERT_EQ(node_cache.used_bytes(), 2 * small);

    node_cache.insert(
        virtual_chunk_offset_t(1, 0, 1), make_node(LARGE_VALUE_BYTES));
    EXPECT_EQ(node_cache.used_bytes(), small + large);

    node_cache.insert(virtual_chunk_offset_t(1, 0, 1), make_node());
    EXPECT_EQ(node_cache.used_bytes(), 2 * small);
    EXPECT_EQ(node_cache.size(), 2);
    EXPECT_EQ(node_cache.stats().evictions, 0u);
}

// Caching a node bigger than the whole budget would evict every other entry
// and then itself, so it is refused and the cache is left alone.
TEST(NodeCache, a_node_larger_than_the_budget_does_not_disturb_the_cache)
{
    NodeCache node_cache(2 * NodeCache::AVERAGE_NODE_SIZE);
    node_cache.insert(virtual_chunk_offset_t(1, 0, 1), make_node());
    node_cache.insert(virtual_chunk_offset_t(2, 0, 1), make_node());
    auto const full = node_cache.used_bytes();
    ASSERT_GT(make_node(LARGE_VALUE_BYTES)->get_mem_size(), full);

    node_cache.insert(
        virtual_chunk_offset_t(3, 0, 1), make_node(LARGE_VALUE_BYTES));

    EXPECT_EQ(node_cache.size(), 2);
    EXPECT_EQ(node_cache.used_bytes(), full);
    EXPECT_EQ(node_cache.stats().evictions, 0u);
    EXPECT_FALSE(node_cache.contains(virtual_chunk_offset_t(3, 0, 1)));
    EXPECT_TRUE(node_cache.contains(virtual_chunk_offset_t(1, 0, 1)));
}

TEST(NodeCache, reports_used_bytes_tracking_the_byte_budget)
{
    NodeCache node_cache(4 * NodeCache::AVERAGE_NODE_SIZE);

    EXPECT_EQ(node_cache.used_bytes(), 0u);

    auto const first = make_node();
    auto const first_size = first->get_mem_size();
    node_cache.insert(virtual_chunk_offset_t(1, 0, 1), first);
    EXPECT_EQ(node_cache.used_bytes(), first_size);

    auto const second = make_node();
    node_cache.insert(virtual_chunk_offset_t(2, 0, 1), second);
    EXPECT_EQ(node_cache.used_bytes(), first_size + second->get_mem_size());
}

// size() reads a mirror of the map, and the byte bound erases from the map
// through the base's eviction primitive, so the two can drift apart.
TEST(NodeCache, size_and_used_bytes_agree_across_both_bounds)
{
    NodeCache node_cache(3 * NodeCache::AVERAGE_NODE_SIZE);

    for (uint32_t i = 1; i <= 8; ++i) {
        // Alternate the size so the slot bound and the byte bound both fire.
        auto const bytes = (i % 2 == 0) ? LARGE_VALUE_BYTES : 84;
        node_cache.insert(virtual_chunk_offset_t(i, 0, 1), make_node(bytes));
        EXPECT_LE(node_cache.used_bytes(), node_cache.max_bytes());
        EXPECT_LE(node_cache.size(), 3);
    }

    EXPECT_GT(node_cache.stats().evictions, 0u);
}

// contains() is the production predicate at find_notify_fiber.cpp, so it has
// to stay off the counters here too.
TEST(NodeCache, contains_does_not_count_as_a_lookup)
{
    NodeCache node_cache(2 * NodeCache::AVERAGE_NODE_SIZE);
    node_cache.insert(virtual_chunk_offset_t(1, 0, 1), make_node());

    EXPECT_TRUE(node_cache.contains(virtual_chunk_offset_t(1, 0, 1)));
    EXPECT_FALSE(node_cache.contains(virtual_chunk_offset_t(2, 0, 1)));

    auto const stats = node_cache.stats();
    EXPECT_EQ(stats.hits, 0u);
    EXPECT_EQ(stats.misses, 0u);
}
