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

#include <category/mpt/util.hpp>

#include <gtest/gtest.h>

#include <compare>
#include <cstdint>
#include <type_traits>

using namespace monad::mpt;

namespace
{
    constexpr uint32_t P = INSERTION_COUNT_PERIOD;

    template <class T>
    concept raw_orderable = requires(T const a, T const b) { a < b; };

    constexpr compact_virtual_chunk_offset_t
    at(uint32_t const count, uint32_t const truncated_offset = 0)
    {
        return compact_virtual_chunk_offset_t::from_count_and_truncated_offset(
            count, truncated_offset);
    }
}

static_assert(P == 0xFFFFE);
static_assert(!std::is_convertible_v<uint32_t, compact_distance>);
static_assert(!std::is_convertible_v<compact_distance, uint32_t>);
static_assert(!raw_orderable<virtual_chunk_offset_t>);
static_assert(!raw_orderable<compact_virtual_chunk_offset_t>);
static_assert(!std::is_convertible_v<compact_virtual_chunk_offset_t, uint32_t>);

TEST(InsertionCount, next_skips_zero_and_max_count)
{
    EXPECT_EQ(next_insertion_count(0), 1u);
    EXPECT_EQ(next_insertion_count(P - 1), P);
    EXPECT_EQ(next_insertion_count(P), 1u);
}

TEST(ChunkListOrder, rank_counts_chunks_from_the_head)
{
    chunk_list_order const before_wrap{P - 2};
    EXPECT_EQ(before_wrap.rank(P - 2), 0u);
    EXPECT_EQ(before_wrap.rank(P), 2u);
    EXPECT_EQ(before_wrap.rank(1), 3u);
    EXPECT_EQ(before_wrap.rank(5), 7u);

    chunk_list_order const fresh{0};
    EXPECT_EQ(fresh.rank(0), 0u);
    EXPECT_EQ(fresh.rank(P - 1), P - 1);

    chunk_list_order const head_at_period{P};
    EXPECT_EQ(head_at_period.rank(P), 0u);
    EXPECT_EQ(head_at_period.rank(1), 1u);

    chunk_list_order const after_wrap{3};
    EXPECT_EQ(after_wrap.rank(3), 0u);
    EXPECT_EQ(after_wrap.rank(P), P - 3);
}

TEST(ChunkListOrder, sentinels_bound_every_live_offset)
{
    chunk_list_order const order{P - 1};
    EXPECT_EQ(order.key(MIN_COMPACT_VIRTUAL_OFFSET), 0u);
    EXPECT_EQ(order.key(INVALID_COMPACT_VIRTUAL_OFFSET), UINT32_MAX);
    EXPECT_TRUE(order.less(MIN_COMPACT_VIRTUAL_OFFSET, at(1, 7)));
    EXPECT_FALSE(order.less(at(1, 7), MIN_COMPACT_VIRTUAL_OFFSET));
    EXPECT_TRUE(order.less(at(1, 7), INVALID_COMPACT_VIRTUAL_OFFSET));
    EXPECT_EQ(order.min(INVALID_COMPACT_VIRTUAL_OFFSET, at(1, 7)), at(1, 7));
    EXPECT_EQ(order.chunks_before(MIN_COMPACT_VIRTUAL_OFFSET), 0u);
}

TEST(ChunkListOrder, orders_across_the_wrap)
{
    chunk_list_order const order{P - 1};
    EXPECT_TRUE(order.less(at(P - 1, 0xfff), at(P, 0)));
    EXPECT_TRUE(order.less(at(P, 0xfff), at(1, 0)));
    EXPECT_TRUE(order.less(at(P, 3), at(P, 4)));
    EXPECT_FALSE(order.less(at(2, 0), at(P, 0)));
    EXPECT_EQ(order.min(at(1, 0), at(P, 5)), at(P, 5));
    EXPECT_EQ(order.chunks_before(at(2, 9)), 3u);
}

TEST(ChunkListOrder, contains_the_chunks_from_the_head_to_the_tail)
{
    chunk_list_order const order{P - 1};
    EXPECT_TRUE(order.contains(at(P - 1, 0), 3));
    EXPECT_TRUE(order.contains(at(1, 0xfff), 3));
    EXPECT_FALSE(order.contains(at(2, 0), 3));
    EXPECT_FALSE(order.contains(at(P - 2, 0xfff), 3));
}

TEST(ChunkListOrder, contains_count_zero_only_while_it_is_the_head)
{
    EXPECT_TRUE(chunk_list_order{0}.contains(MIN_COMPACT_VIRTUAL_OFFSET, 1));
    EXPECT_TRUE(chunk_list_order{0}.contains(at(0, 5), 1));
    EXPECT_FALSE(chunk_list_order{P - 1}.contains(at(0, 5), 4));
    EXPECT_FALSE(chunk_list_order{P}.contains(at(0, 5), 4));
}

TEST(ChunkListOrder, distance_spans_the_wrap)
{
    chunk_list_order const order{P - 1};
    EXPECT_EQ(
        units(order.distance(at(P - 1, 0x100), at(1, 0x80))),
        (2u << 12) - 0x80);
    EXPECT_EQ(units(order.distance(at(P, 0xf00), at(1, 0x10))), 0x110u);
    EXPECT_EQ(bytes(compact_distance{3}), 3ull << 16);
}

TEST(ChunkListOrder, advance_steps_over_the_skipped_counts)
{
    chunk_list_order const order{P - 1};
    EXPECT_EQ(
        order.advance(at(P, 0xf80), compact_distance{0x100}), at(1, 0x80));
    EXPECT_EQ(order.advance(at(P - 1, 0xfff), compact_distance{1}), at(P, 0));
    EXPECT_EQ(order.advance(at(1, 2), compact_distance{0}), at(1, 2));
}

TEST(ChunkListOrder, advance_keeps_the_head_chunk_count)
{
    chunk_list_order const fresh{0};
    EXPECT_EQ(
        fresh.advance(MIN_COMPACT_VIRTUAL_OFFSET, compact_distance{5}),
        at(0, 5));
    EXPECT_EQ(fresh.advance(at(0, 0xfff), compact_distance{1}), at(1, 0));

    chunk_list_order const head_at_period{P};
    EXPECT_EQ(head_at_period.advance(at(P, 1), compact_distance{2}), at(P, 3));
}

TEST(ChunkListOrder, matches_raw_arithmetic_before_any_wrap)
{
    chunk_list_order const order{1000};
    auto const a = at(1000, 0x123);
    auto const b = at(1003, 0x456);
    EXPECT_EQ(
        order.less(a, b), static_cast<uint32_t>(a) < static_cast<uint32_t>(b));
    EXPECT_EQ(
        units(order.distance(a, b)),
        static_cast<uint32_t>(b) - static_cast<uint32_t>(a));
    EXPECT_EQ(
        static_cast<uint32_t>(order.advance(a, compact_distance{0x5000})),
        static_cast<uint32_t>(a) + 0x5000);
}

TEST(OffsetOrder, compares_virtual_offsets_by_list_then_rank)
{
    offset_order const order{chunk_list_order{P - 1}, chunk_list_order{1}};
    virtual_chunk_offset_t const fast_old{P - 1, 100, 1};
    virtual_chunk_offset_t const fast_new{1, 0, 1};
    virtual_chunk_offset_t const slow{1, 0, 0};
    virtual_chunk_offset_t const slow_new{3, 0, 0};
    EXPECT_TRUE(std::is_lt(order.compare(fast_old, fast_new)));
    EXPECT_TRUE(std::is_gt(order.compare(fast_new, fast_old)));
    EXPECT_TRUE(std::is_eq(order.compare(fast_new, fast_new)));
    EXPECT_TRUE(std::is_lt(order.compare(slow, fast_old)));
    EXPECT_TRUE(std::is_lt(order.compare(slow, slow_new)));
    EXPECT_TRUE(std::is_lt(order.compare(
        virtual_chunk_offset_t{1, 10, 1}, virtual_chunk_offset_t{1, 20, 1})));
}

TEST(ChunkListOrder, factory_matches_the_virtual_offset_conversion)
{
    virtual_chunk_offset_t const v{5, 0x1234567, 1};
    EXPECT_EQ(compact_virtual_chunk_offset_t{v}, at(5, 0x123));
    EXPECT_EQ(at(5, 0x123).get_count(), 5u);
    EXPECT_EQ(at(5, 0x123).get_truncated_offset(), 0x123u);
}

// Every fast pair below orders the other way under the slow head, and every
// slow pair the other way under the fast head.
TEST(OffsetOrder, pair_helpers_use_each_lists_order)
{
    offset_order const order{chunk_list_order{P - 1}, chunk_list_order{7}};
    compact_offset_pair const threshold{at(8, 0), at(P - 1, 0)};
    compact_offset_pair const old_fast{
        at(6, 0), INVALID_COMPACT_VIRTUAL_OFFSET};
    compact_offset_pair const old_slow{
        INVALID_COMPACT_VIRTUAL_OFFSET, at(P - 2, 0)};
    EXPECT_TRUE(order.any_below(old_fast, threshold));
    EXPECT_TRUE(order.fast_below(old_fast, threshold));
    EXPECT_TRUE(order.any_below(old_slow, threshold));
    EXPECT_FALSE(order.fast_below(old_slow, threshold));
    EXPECT_FALSE(order.any_below({at(9, 0), at(P, 0)}, threshold));
    EXPECT_EQ(
        order.min({at(6, 0), at(P - 1, 0)}, {at(8, 0), at(P - 2, 0)}),
        (compact_offset_pair{at(6, 0), at(P - 2, 0)}));
}

TEST(OffsetOrder, below_uses_the_offsets_own_list_and_threshold)
{
    offset_order const order{chunk_list_order{P - 1}, chunk_list_order{7}};
    compact_offset_pair const threshold{at(8, 0), at(P - 1, 0)};
    EXPECT_TRUE(order.below(virtual_chunk_offset_t{6, 0, 1}, threshold));
    EXPECT_FALSE(order.below(virtual_chunk_offset_t{9, 0, 1}, threshold));
    EXPECT_TRUE(order.below(virtual_chunk_offset_t{P - 2, 0, 0}, threshold));
    EXPECT_FALSE(order.below(virtual_chunk_offset_t{P, 0, 0}, threshold));
}
