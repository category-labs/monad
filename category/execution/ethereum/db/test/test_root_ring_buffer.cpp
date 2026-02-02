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

#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/mpt/node.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::mpt;

// Helper to create a test node
std::shared_ptr<Node> make_test_node(uint64_t const version)
{
    return make_node(
        0, {}, NibblesView{}, std::nullopt, 0, static_cast<int64_t>(version));
}

class RootRingBufferTest : public ::testing::Test
{
protected:
    RootRingBuffer<5> buffer_;
};

// Test basic sequential insertion and retrieval
TEST_F(RootRingBufferTest, SequentialInsertion)
{
    auto node0 = make_test_node(0);
    auto node1 = make_test_node(1);
    auto node2 = make_test_node(2);

    buffer_.insert(0, node0);
    buffer_.insert(1, node1);
    buffer_.insert(2, node2);

    EXPECT_EQ(buffer_.find(0), node0);
    EXPECT_EQ(buffer_.find(1), node1);
    EXPECT_EQ(buffer_.find(2), node2);
}

// Test eviction when buffer is full
TEST_F(RootRingBufferTest, Eviction)
{
    for (uint64_t i = 0; i < 10; ++i) {
        buffer_.insert(i, make_test_node(i));
    }

    // Only last 5 should remain
    EXPECT_EQ(buffer_.find(4), nullptr); // evicted
    EXPECT_NE(buffer_.find(5), nullptr);
    EXPECT_NE(buffer_.find(9), nullptr);
}

// Test small gap insertion (gap < N)
TEST_F(RootRingBufferTest, SmallGap)
{
    auto node0 = make_test_node(0);
    auto node3 = make_test_node(3);

    buffer_.insert(0, node0);
    buffer_.insert(3, node3); // gap of 2 blocks

    EXPECT_EQ(buffer_.find(0), node0);
    EXPECT_EQ(buffer_.find(3), node3);
    // Gaps should be cleared
    EXPECT_EQ(buffer_.find(1), nullptr);
    EXPECT_EQ(buffer_.find(2), nullptr);
}

// Test large gap insertion (gap >= N) - should be O(1) not O(gap)
TEST_F(RootRingBufferTest, LargeGap)
{
    auto node0 = make_test_node(0);
    auto node1000 = make_test_node(1000);

    buffer_.insert(0, node0);
    buffer_.insert(1000, node1000); // large gap

    // Old nodes should be cleared
    EXPECT_EQ(buffer_.find(0), nullptr);
    // New node should be present
    EXPECT_EQ(buffer_.find(1000), node1000);
}

// Test out of range insertion (too old to cache)
TEST_F(RootRingBufferTest, OutOfRange)
{
    auto node10 = make_test_node(10);
    auto node5 = make_test_node(5);

    buffer_.insert(10, node10);
    buffer_.insert(5, node5); // too old (10 - 5 > N-1)

    EXPECT_EQ(buffer_.find(5), nullptr); // should be ignored
    EXPECT_EQ(buffer_.find(10), node10);
}

// Test wraparound behavior
TEST_F(RootRingBufferTest, Wraparound)
{
    for (uint64_t i = 0; i < 20; ++i) {
        buffer_.insert(i, make_test_node(i));
    }

    // Only last 5 should be cached
    EXPECT_EQ(buffer_.find(14), nullptr);
    EXPECT_NE(buffer_.find(15), nullptr);
    EXPECT_NE(buffer_.find(19), nullptr);
}
