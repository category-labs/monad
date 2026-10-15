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

#include <category/async/config.hpp>
#include <category/async/io.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>
#include <category/mpt/detail/db_metadata.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/node_cache.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/util.hpp>

#include <gtest/gtest.h>

#include <chrono>
#include <cstdint>
#include <cstring>
#include <memory>
#include <optional>
#include <utility>

using namespace monad::mpt;
using namespace monad::literals;

namespace
{
    constexpr uint32_t P = INSERTION_COUNT_PERIOD;
    constexpr std::chrono::steady_clock::time_point T0{};

    std::shared_ptr<Node> make_cache_node(uint32_t const v)
    {
        monad::byte_string value(84, 0);
        memcpy(value.data(), &v, 4);
        std::shared_ptr<Node> node =
            monad::mpt::make_node(0, {}, {}, std::move(value), 0, 0);
        MONAD_ASSERT(node->get_mem_size() == NodeCache::AVERAGE_NODE_SIZE);
        return node;
    }

    uint32_t cached_value(NodeCache::ConstAccessor const &acc)
    {
        auto const view(acc->second->val.first->value());
        MONAD_ASSERT(84 == view.size());
        return *(uint32_t const *)view.data();
    }

    class NodeCacheOnPool : public ::testing::Test
    {
    protected:
        monad::async::storage_pool pool{
            monad::async::use_anonymous_inode_tag{}};
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers buffers{
            monad::io::make_buffers_for_segregated_read_write(
                ring1, ring2, 2, 4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE)};
        monad::async::AsyncIO io{pool, buffers};
        UpdateAux aux{};

        NodeCacheOnPool()
        {
            aux.init(io, 50);
        }

        void append_free_chunk(UpdateAux::chunk_list const list)
        {
            auto &ctx = aux.metadata_ctx();
            uint32_t const idx = ctx.main()->free_list_end()->index(ctx.main());
            ctx.remove(idx);
            ctx.append(list, idx);
        }

        void release_tail(UpdateAux::chunk_list const list)
        {
            auto const *const m = aux.metadata_ctx().main();
            release(
                list == UpdateAux::chunk_list::fast ? m->fast_list.end
                                                    : m->slow_list.end);
        }

        void release_head(UpdateAux::chunk_list const list)
        {
            auto const *const m = aux.metadata_ctx().main();
            release(
                list == UpdateAux::chunk_list::fast ? m->fast_list.begin
                                                    : m->slow_list.begin);
        }

    private:
        void release(uint32_t const idx)
        {
            auto &ctx = aux.metadata_ctx();
            ctx.remove(idx);
            ctx.append(UpdateAux::chunk_list::free, idx);
        }
    };

    std::optional<fast_slow_list_counts>
    counts(chunk_list_counts const fast, chunk_list_counts const slow)
    {
        return fast_slow_list_counts{fast, slow};
    }
}

TEST_F(NodeCacheOnPool, works)
{
    NodeCache node_cache(3 * NodeCache::AVERAGE_NODE_SIZE, aux);
    NodeCache::ConstAccessor acc;

    node_cache.insert(virtual_chunk_offset_t(1, 0, 1), make_cache_node(0x123));
    node_cache.insert(virtual_chunk_offset_t(2, 0, 1), make_cache_node(0xdead));
    node_cache.insert(virtual_chunk_offset_t(3, 0, 1), make_cache_node(0xbeef));
    EXPECT_EQ(node_cache.size(), 3);

    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(3, 0, 1)));
    EXPECT_EQ(cached_value(acc), 0xbeef);
    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(2, 0, 1)));
    EXPECT_EQ(cached_value(acc), 0xdead);
    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(1, 0, 1)));
    EXPECT_EQ(cached_value(acc), 0x123);

    node_cache.insert(virtual_chunk_offset_t(4, 0, 1), make_cache_node(0xcafe));
    EXPECT_EQ(node_cache.size(), 3);

    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(2, 0, 1)));
    EXPECT_EQ(cached_value(acc), 0xdead);
    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(1, 0, 1)));
    EXPECT_EQ(cached_value(acc), 0x123);
    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(4, 0, 1)));
    EXPECT_EQ(cached_value(acc), 0xcafe);

    node_cache.insert(
        virtual_chunk_offset_t(2, 0, 1), make_cache_node(0xc0ffee));
    node_cache.insert(virtual_chunk_offset_t(5, 0, 1), make_cache_node(100));
    EXPECT_EQ(node_cache.size(), 3);

    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(2, 0, 1)));
    EXPECT_EQ(cached_value(acc), 0xc0ffee);
    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(4, 0, 1)));
    EXPECT_EQ(cached_value(acc), 0xcafe);
    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(5, 0, 1)));
    EXPECT_EQ(cached_value(acc), 100);

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
    node_cache.insert(virtual_chunk_offset_t(1, 0, 1), make_cache_node(0x123));
    EXPECT_EQ(node_cache.size(), 1);
    node_cache.insert(virtual_chunk_offset_t(1, 0, 0), make_cache_node(0xdead));
    EXPECT_EQ(node_cache.size(), 2);
    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(1, 0, 1)));
    EXPECT_EQ(cached_value(acc), 0x123);
    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(1, 0, 0)));
    EXPECT_EQ(cached_value(acc), 0xdead);
}

TEST_F(NodeCacheOnPool, a_lookup_after_either_tail_moves_back_forgets_entries)
{
    append_free_chunk(UpdateAux::chunk_list::fast);
    append_free_chunk(UpdateAux::chunk_list::slow);
    NodeCache node_cache(3 * NodeCache::AVERAGE_NODE_SIZE, aux);
    NodeCache::ConstAccessor acc;
    virtual_chunk_offset_t const key{0, 0, 1};

    node_cache.insert(key, make_cache_node(1));
    EXPECT_TRUE(node_cache.find(acc, key));
    release_tail(UpdateAux::chunk_list::fast);
    EXPECT_FALSE(node_cache.find(acc, key));

    node_cache.insert(key, make_cache_node(2));
    EXPECT_TRUE(node_cache.find(acc, key));
    release_tail(UpdateAux::chunk_list::slow);
    EXPECT_FALSE(node_cache.find(acc, key));
}

TEST_F(
    NodeCacheOnPool,
    an_entry_cached_again_after_forgetting_survives_newer_inserts)
{
    append_free_chunk(UpdateAux::chunk_list::fast);
    NodeCache node_cache(3 * NodeCache::AVERAGE_NODE_SIZE, aux);
    NodeCache::ConstAccessor acc;
    virtual_chunk_offset_t const absent{9, 0, 1};

    EXPECT_FALSE(node_cache.find(acc, absent));
    node_cache.insert(virtual_chunk_offset_t(P - 1, 0, 1), make_cache_node(1));
    node_cache.insert(virtual_chunk_offset_t(P, 0, 1), make_cache_node(2));
    node_cache.insert(virtual_chunk_offset_t(5, 0, 0), make_cache_node(3));
    release_tail(UpdateAux::chunk_list::fast);
    EXPECT_FALSE(node_cache.find(acc, absent));

    node_cache.insert(virtual_chunk_offset_t(5, 0, 0), make_cache_node(4));
    node_cache.insert(virtual_chunk_offset_t(1, 0, 1), make_cache_node(5));
    node_cache.insert(virtual_chunk_offset_t(1, 64, 1), make_cache_node(6));
    ASSERT_TRUE(node_cache.find(acc, virtual_chunk_offset_t(5, 0, 0)));
    EXPECT_EQ(cached_value(acc), 4u);
    EXPECT_EQ(node_cache.size(), 3u);
}

TEST_F(NodeCacheOnPool, a_tail_chunk_back_with_a_new_count_is_checked)
{
    append_free_chunk(UpdateAux::chunk_list::fast);
    auto const *const m = aux.metadata_ctx().main();
    uint32_t const recycled = m->fast_list.end;
    NodeCache node_cache(3 * NodeCache::AVERAGE_NODE_SIZE, aux);
    NodeCache::ConstAccessor acc;

    // The free list is a stack, so the released chunk is the next tail.
    append_free_chunk(UpdateAux::chunk_list::fast);
    release_head(UpdateAux::chunk_list::fast);
    release_head(UpdateAux::chunk_list::fast);
    append_free_chunk(UpdateAux::chunk_list::fast);
    ASSERT_EQ(m->fast_list.end, recycled);
    virtual_chunk_offset_t const key{3, 0, 1};
    EXPECT_FALSE(node_cache.find(acc, key));
    node_cache.insert(key, make_cache_node(1));

    release_tail(UpdateAux::chunk_list::fast);
    EXPECT_FALSE(node_cache.find(acc, key));
}

TEST_F(NodeCacheOnPool, a_writer_stopped_mid_append_empties_the_cache_once)
{
    NodeCache node_cache(3 * NodeCache::AVERAGE_NODE_SIZE, aux);
    NodeCache::ConstAccessor acc;
    virtual_chunk_offset_t const key{0, 0, 1};
    node_cache.insert(key, make_cache_node(1));

    auto const *const m = aux.metadata_ctx().main();
    uint32_t const tail = m->fast_list.end;
    uint32_t const free_chunk = m->free_list_end()->index(m);
    auto const set_fast_tail = [&](uint32_t const id) {
        aux.metadata_ctx().modify_metadata(
            [](detail::db_metadata *md, uint32_t v) { md->fast_list.end = v; },
            id);
    };
    ASSERT_TRUE(aux.list_counts().has_value());

    // An append publishes the new tail id before that chunk's info.
    set_fast_tail(free_chunk);
    EXPECT_FALSE(node_cache.find(acc, key));
    node_cache.insert(key, make_cache_node(2));
    EXPECT_TRUE(node_cache.find(acc, key));

    set_fast_tail(tail);
    EXPECT_FALSE(node_cache.find(acc, key));
}

TEST(
    CountReuseWatch,
    forgets_once_a_tail_reaches_the_head_seen_at_the_last_forget)
{
    CountReuseWatch watch{std::chrono::hours{1}};
    EXPECT_TRUE(watch.must_forget(counts({P - 1, 2}, {5, 9}), T0));
    EXPECT_FALSE(watch.must_forget(counts({P, 100}, {5, 9}), T0));
    EXPECT_FALSE(watch.must_forget(counts({1, P - 2}, {5, 9}), T0));
    EXPECT_TRUE(watch.must_forget(counts({3, P - 1}, {5, 9}), T0));
}

TEST(CountReuseWatch, a_backward_tail_on_either_list_forgets)
{
    CountReuseWatch watch{std::chrono::hours{1}};
    EXPECT_TRUE(watch.must_forget(counts({10, 20}, {5, 9}), T0));
    EXPECT_TRUE(watch.must_forget(counts({10, 18}, {5, 9}), T0));
    EXPECT_FALSE(watch.must_forget(counts({10, 18}, {5, 12}), T0));
    EXPECT_TRUE(watch.must_forget(counts({10, 18}, {5, 6}), T0));
}

TEST(CountReuseWatch, a_single_chunk_list_forgets_only_after_a_lap)
{
    CountReuseWatch watch{std::chrono::hours{1}};
    EXPECT_TRUE(watch.must_forget(counts({10, 20}, {5, 5}), T0));
    EXPECT_FALSE(watch.must_forget(counts({10, 20}, {5, 6}), T0));
    EXPECT_FALSE(watch.must_forget(counts({10, 21}, {5, 7}), T0));
}

TEST(CountReuseWatch, unreadable_counts_forget_and_record_nothing)
{
    CountReuseWatch watch{std::chrono::hours{1}};
    EXPECT_TRUE(watch.must_forget(counts({10, 20}, {5, 9}), T0));
    EXPECT_TRUE(watch.must_forget(std::nullopt, T0));
    EXPECT_TRUE(watch.must_forget(counts({10, 20}, {5, 9}), T0));
    EXPECT_FALSE(watch.must_forget(counts({10, 20}, {5, 9}), T0));
}

TEST(CountReuseWatch, a_check_later_than_the_fastest_lap_forgets)
{
    using namespace std::chrono_literals;
    CountReuseWatch watch{1h};
    EXPECT_TRUE(watch.must_forget(counts({10, 20}, {5, 9}), T0));
    EXPECT_FALSE(watch.must_forget(counts({11, 21}, {5, 9}), T0 + 30min));
    EXPECT_TRUE(watch.must_forget(counts({11, 22}, {5, 9}), T0 + 91min));
}
