// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/hex.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/scratch_pool.hpp>
#include <category/mpt/upward_tnode.hpp>
#include <category/mpt/util.hpp>

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <vector>

using namespace monad::mpt;
using namespace monad::literals;

namespace
{
    class ScratchPoolCaching : public ::testing::Test
    {
    protected:
        void SetUp() override
        {
            if (!ScratchPool::caching) {
                GTEST_SKIP() << "ASAN builds bypass the cache";
            }
        }
    };
}

TEST_F(ScratchPoolCaching, reuses_freed_block_of_same_size_class)
{
    ScratchPool pool;
    void *const a = pool.allocate(200);
    auto const addr = reinterpret_cast<uintptr_t>(a);
    pool.deallocate(a, 200);
    EXPECT_EQ(pool.cached_bytes(), 256);
    void *const b = pool.allocate(193);
    EXPECT_EQ(reinterpret_cast<uintptr_t>(b), addr);
    EXPECT_EQ(pool.cached_bytes(), 0);
    pool.deallocate(b, 193);
}

TEST_F(ScratchPoolCaching, does_not_reuse_block_of_other_size_class)
{
    ScratchPool pool;
    void *const a = pool.allocate(64);
    auto const addr = reinterpret_cast<uintptr_t>(a);
    pool.deallocate(a, 64);
    void *const b = pool.allocate(65);
    EXPECT_NE(reinterpret_cast<uintptr_t>(b), addr);
    pool.deallocate(b, 65);
    EXPECT_EQ(pool.cached_bytes(), 64 + 128);
}

TEST_F(ScratchPoolCaching, cached_bytes_are_capped)
{
    ScratchPool pool;
    constexpr size_t block = ScratchPool::max_cached_block;
    constexpr size_t count = ScratchPool::max_cached_bytes / block + 10;
    std::vector<void *> blocks;
    blocks.reserve(count);
    for (size_t i = 0; i < count; ++i) {
        blocks.push_back(pool.allocate(block));
    }
    for (void *const p : blocks) {
        pool.deallocate(p, block);
    }
    EXPECT_EQ(pool.cached_bytes(), ScratchPool::max_cached_bytes);
}

TEST_F(ScratchPoolCaching, freed_tnode_block_is_reused)
{
    auto const key = 0xabcd_bytes;
    auto first = UpdateTNode::make(0b11, nullptr, INVALID_BRANCH, key);
    auto const addr = reinterpret_cast<uintptr_t>(first.get());
    first->npending = 0;
    first.reset();
    auto second = UpdateTNode::make(0b101, nullptr, INVALID_BRANCH, key);
    EXPECT_EQ(reinterpret_cast<uintptr_t>(second.get()), addr);
    second->npending = 0;
}

TEST(ScratchPool, large_blocks_bypass_cache)
{
    ScratchPool pool;
    void *const a = pool.allocate(ScratchPool::max_cached_block + 1);
    pool.deallocate(a, ScratchPool::max_cached_block + 1);
    EXPECT_EQ(pool.cached_bytes(), 0);
}

TEST(ScratchPool, zero_byte_block_round_trips)
{
    ScratchPool pool;
    void *const a = pool.allocate(0);
    EXPECT_NE(a, nullptr);
    pool.deallocate(a, 0);
}

TEST(UpdateTNode, children_and_path_live_in_one_block)
{
    auto const key = 0x123456789a_bytes;
    // Odd start nibble, odd length.
    NibblesView const path = NibblesView{key}.substr(1, 7);
    uint16_t const mask = 0b1000'0100'0010'0001;
    auto tnode = UpdateTNode::make(mask, nullptr, INVALID_BRANCH, path, 7);
    EXPECT_EQ(tnode->children.size(), 4);
    for (ChildData const &child : tnode->children) {
        EXPECT_FALSE(child.is_valid());
        EXPECT_EQ(child.ptr, nullptr);
    }
    EXPECT_EQ(tnode->path, path);
    EXPECT_EQ(tnode->npending, 4);
    EXPECT_EQ(tnode->version, 7);
    auto const *const begin = reinterpret_cast<std::byte const *>(tnode.get());
    EXPECT_EQ(
        reinterpret_cast<std::byte const *>(tnode->children.data()),
        begin + sizeof(UpdateTNode));
    EXPECT_EQ(
        tnode->path.data(),
        reinterpret_cast<unsigned char const *>(
            tnode->children.data() + tnode->children.size()));
    tnode->npending = 0;
}

TEST(UpdateTNode, path_copy_keeps_nibble_range)
{
    auto const key = 0x123456789a_bytes;
    NibblesView const full{key};
    for (NibblesView const path :
         {NibblesView{}, full.substr(2, 5), full.substr(3, 4), full}) {
        auto const tnode = UpdateTNode::make(0, nullptr, INVALID_BRANCH, path);
        EXPECT_TRUE(tnode->children.empty());
        EXPECT_EQ(tnode->path, path);
    }
}
