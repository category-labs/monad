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

#include <category/core/byte_string.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/node_cache.hpp>

#include <gtest/gtest.h>

#include <cstdint>

using namespace monad::mpt;
using namespace monad::literals;

TEST(NodeCache, works)
{
    NodeCache node_cache(3 * NodeCache::AVERAGE_NODE_SIZE);
    NodeCache::ConstAccessor acc;

    auto make_node = [&](uint32_t v) {
        monad::byte_string value(84, 0);
        memcpy(value.data(), &v, 4);
        std::shared_ptr<CacheNode> node = copy_node<CacheNode>(
            monad::mpt::make_node(0, {}, {}, std::move(value), 0, 0).get());
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
    auto node = copy_node<CacheNode>(
        monad::mpt::make_node(0, {}, {}, std::move(large_value), 0, 0).get());
    EXPECT_EQ(node->get_mem_size(), 272);
    node_cache.insert(virtual_chunk_offset_t(6, 0, 1), std::move(node));
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
