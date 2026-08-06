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

#include <category/async/config.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/parallel_upsert.hpp>
#include <category/mpt/util.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <atomic>
#include <barrier>
#include <cstddef>
#include <cstdint>
#include <thread>
#include <utility>
#include <vector>

#include <stdlib.h>
#include <unistd.h>

using namespace ::monad::mpt;
using namespace ::monad::async;

namespace
{
    constexpr size_t EXTENT_BYTES = 4096;

    // A pathless valueless leaf costs this much beyond its value
    constexpr uint32_t LEAF_OVERHEAD = 20;

    Node::SharedPtr
    make_leaf_node_with_value_size(size_t const value_size, unsigned const seed)
    {
        monad::byte_string const value(
            value_size, static_cast<unsigned char>(seed));
        return make_node(0, {}, NibblesView{}, value, {}, 0);
    }

    Node::SharedPtr read_node_at(storage_pool &pool, chunk_offset_t const at)
    {
        // The spare bits say how many pages the node needs, so a read that
        // deserializes proves them right as well as the offset
        size_t const bytes_to_read =
            size_t{node_disk_pages_spare_15{at}.to_pages() << DISK_PAGE_BITS};
        auto const read_from =
            round_down_align<DISK_PAGE_BITS>(file_offset_t{at.offset});
        auto const offset_in_page = size_t{at.offset - read_from};
        auto const [fd, chunk_base] =
            pool.chunk(storage_pool::seq, static_cast<uint32_t>(at.id))
                .read_fd();
        auto *const buffer = static_cast<unsigned char *>(
            ::aligned_alloc(DISK_PAGE_SIZE, bytes_to_read));
        MONAD_ASSERT(buffer != nullptr);
        ssize_t const bytes_read = ::pread(
            fd,
            buffer,
            bytes_to_read,
            static_cast<off_t>(chunk_base + read_from));
        MONAD_ASSERT(bytes_read == static_cast<ssize_t>(bytes_to_read));
        auto node = deserialize_node_from_buffer(
            buffer + offset_in_page, bytes_to_read - offset_in_page);
        ::free(buffer);
        return node;
    }

    constexpr uint32_t NO_GRANT = uint32_t(-1);

    // Production reserves through the context's locked allocator, so the tests
    // drive that one rather than a reimplementation of its clamping
    struct Extents
    {
        ParallelUpsertContext ctx{1, 2};
        unsigned grants{0};

        Extents(
            storage_pool &pool, uint32_t const chunk_id,
            uint32_t const grant_chunk_id)
        {
            ctx.init_extents(
                pool, chunk_id, /*in_fast_list=*/true, [this, grant_chunk_id] {
                    MONAD_ASSERT(grant_chunk_id != NO_GRANT);
                    ++grants;
                    return grant_chunk_id;
                });
        }

        WorkerNodeWriter::ExtentSource source()
        {
            return [this](size_t const min_bytes, size_t const want_bytes) {
                return ctx.reserve_extent(min_bytes, want_bytes);
            };
        }
    };

    // Hammers reserve_extent from two threads against chunks left with only
    // `tail_bytes` free, returning every reservation made, sorted by placement.
    std::vector<ExtentReservation>
    reserve_concurrently(storage_pool &pool, size_t const tail_bytes)
    {
        auto const leave_only_the_tail = [&pool,
                                          tail_bytes](uint32_t const id) {
            auto &chunk = pool.chunk(storage_pool::seq, id);
            (void)chunk.reserve(chunk.capacity() - tail_bytes);
            return id;
        };
        ParallelUpsertContext ctx{1, 2};
        std::atomic<uint32_t> next_chunk_id{1};
        ctx.init_extents(
            pool, leave_only_the_tail(0), /*in_fast_list=*/true, [&] {
                return leave_only_the_tail(
                    next_chunk_id.fetch_add(1, std::memory_order_relaxed));
            });

        constexpr unsigned reservers = 2;
        constexpr unsigned per_reserver = 256;
        std::vector<ExtentReservation> reserved[reservers];
        std::barrier sync{static_cast<ptrdiff_t>(reservers)};
        std::vector<std::thread> threads;
        for (auto &out : reserved) {
            out.reserve(per_reserver);
            // No gtest ASSERT_* in here: it returns from the lambda, and the
            // peer then waits on the barrier forever, which has no timeout
            threads.emplace_back([&ctx, &out, &sync] {
                for (unsigned n = 0; n < per_reserver; ++n) {
                    // Enter the read-then-reserve window together every time,
                    // so an implementation that leaves it unguarded loses the
                    // race rather than getting away with it
                    sync.arrive_and_wait();
                    out.push_back(
                        ctx.reserve_extent(DISK_PAGE_SIZE, DISK_PAGE_SIZE));
                }
            });
        }
        for (auto &thread : threads) {
            thread.join();
        }

        std::vector<ExtentReservation> all;
        for (auto const &out : reserved) {
            all.insert(all.end(), out.begin(), out.end());
        }
        EXPECT_EQ(all.size(), reservers * per_reserver);
        EXPECT_GT(next_chunk_id.load(), 1u); // the run did cross chunks
        std::ranges::sort(all, [](auto const &a, auto const &b) {
            return a.chunk_id != b.chunk_id ? a.chunk_id < b.chunk_id
                                            : a.base < b.base;
        });
        return all;
    }

    // Returns how many neighbouring pairs of one chunk it compared, so a caller
    // can prove the disjointness check was not vacuous.
    unsigned check_placement(
        storage_pool &pool, std::vector<ExtentReservation> const &all)
    {
        unsigned compared = 0;
        for (size_t n = 0; n < all.size(); ++n) {
            auto const &at = all[n];
            EXPECT_EQ(at.bytes, DISK_PAGE_SIZE);
            EXPECT_LE(
                at.base + at.bytes,
                pool.chunk(storage_pool::seq, at.chunk_id).capacity());
            if (n > 0 && all[n - 1].chunk_id == at.chunk_id) {
                EXPECT_LE(all[n - 1].base + all[n - 1].bytes, at.base);
                ++compared;
            }
        }
        return compared;
    }
}

TEST(WorkerNodeWriter, appends_and_reads_back_across_extents)
{
    storage_pool pool(use_anonymous_inode_tag{});
    // Leave the starting chunk room for one whole extent plus a remainder too
    // small for one, so the run crosses an extent boundary, a clamped extent
    // and a chunk boundary
    auto &first_chunk = pool.chunk(storage_pool::seq, 0);
    (void)first_chunk.reserve(
        first_chunk.capacity() - EXTENT_BYTES - EXTENT_BYTES / 2);

    Extents extents{pool, 0, 1};
    WorkerNodeWriter writer{pool, EXTENT_BYTES, extents.source()};
    // Where the first extent must land, sampled from the allocator itself
    auto const first_extent_base = first_chunk.reserved_bytes();

    // Wide enough that an extent holds only a handful, and of differing sizes
    // so that node placement within a page varies
    std::vector<std::pair<chunk_offset_t, Node::SharedPtr>> written;
    for (unsigned n = 0; n < 64; ++n) {
        auto node = make_leaf_node_with_value_size(400 + 13 * n, n);
        auto const at = writer.append(*node);
        written.emplace_back(at, std::move(node));
    }
    writer.flush();

    EXPECT_GT(extents.grants, 0u);
    // A base_ error shared by append and flush would round trip fine, so pin
    // the first node to where the allocator's cursor stood before it was
    // written
    EXPECT_EQ(written.front().first.offset, first_extent_base);
    for (auto const &[at, node] : written) {
        auto const read = read_node_at(pool, at);
        EXPECT_EQ(read->get_disk_size(), node->get_disk_size());
        EXPECT_EQ(read->value(), node->value());
    }

    // A round trip alone would still pass if append and flush agreed on the
    // same wrong base, so check the offsets against what was reserved and
    // against each other
    for (size_t n = 0; n < written.size(); ++n) {
        auto const &[at, node] = written[n];
        auto const size = node->get_disk_size();
        auto const &chunk =
            pool.chunk(storage_pool::seq, static_cast<uint32_t>(at.id));
        EXPECT_LE(at.offset + size, chunk.reserved_bytes());
        if (n > 0) {
            auto const &[prev_at, prev_node] = written[n - 1];
            if (prev_at.id == at.id) {
                EXPECT_LE(
                    prev_at.offset + prev_node->get_disk_size(), at.offset);
            }
        }
    }
}

TEST(WorkerNodeWriter, flush_mid_extent_retains_it_for_later_appends)
{
    storage_pool pool(use_anonymous_inode_tag{});
    // A non-zero extent base, so an offset that forgets it is visible
    (void)pool.chunk(storage_pool::seq, 0).reserve(2 * EXTENT_BYTES);
    Extents extents{pool, 0, NO_GRANT};
    WorkerNodeWriter writer{pool, EXTENT_BYTES, extents.source()};

    auto const first = make_leaf_node_with_value_size(512, 1);
    auto const first_at = writer.append(*first);
    writer.flush();
    auto const second = make_leaf_node_with_value_size(512, 2);
    auto const second_at = writer.append(*second);
    writer.flush();

    // Still the same extent, and the second node begins on the page boundary
    // the first flush ended on: the two writes are disjoint and contiguous
    EXPECT_EQ(second_at.id, first_at.id);
    EXPECT_EQ(
        second_at.offset,
        round_up_align<DISK_PAGE_BITS>(
            file_offset_t{first_at.offset} + first->get_disk_size()));
    EXPECT_LT(second_at.offset, first_at.offset + EXTENT_BYTES);

    EXPECT_EQ(read_node_at(pool, first_at)->value(), first->value());
    EXPECT_EQ(read_node_at(pool, second_at)->value(), second->value());
}

TEST(WorkerNodeWriter, spare_pages_cover_a_node_that_starts_mid_page)
{
    storage_pool pool(use_anonymous_inode_tag{});
    Extents extents{pool, 0, NO_GRANT};
    WorkerNodeWriter writer{pool, EXTENT_BYTES, extents.source()};

    // A 500 byte filler leaves the next node starting 500 bytes into a page, so
    // a 532 byte node then spans three pages where a page aligned one of the
    // same size would need two
    auto const filler = make_leaf_node_with_value_size(500 - LEAF_OVERHEAD, 1);
    ASSERT_EQ(filler->get_disk_size(), 500u);
    (void)writer.append(*filler);
    auto const straddling = make_leaf_node_with_value_size(512, 2);
    ASSERT_EQ(straddling->get_disk_size(), 532u);
    auto const at = writer.append(*straddling);
    ASSERT_EQ(at.offset % DISK_PAGE_SIZE, 500u);
    EXPECT_EQ(node_disk_pages_spare_15{at}.to_pages(), 3u);
    writer.flush();

    EXPECT_EQ(read_node_at(pool, at)->value(), straddling->value());
}

TEST(WorkerNodeWriter, node_larger_than_the_extent_gets_its_own_reservation)
{
    storage_pool pool(use_anonymous_inode_tag{});
    Extents extents{pool, 0, NO_GRANT};
    WorkerNodeWriter writer{pool, EXTENT_BYTES, extents.source()};

    auto const node = make_leaf_node_with_value_size(4 * EXTENT_BYTES, 0);
    auto const at = writer.append(*node);
    writer.flush();

    auto const read = read_node_at(pool, at);
    EXPECT_EQ(read->value(), node->value());
}

TEST(WorkerNodeWriter, oversized_node_leaves_the_buffered_extent_intact)
{
    storage_pool pool(use_anonymous_inode_tag{});
    Extents extents{pool, 0, NO_GRANT};
    WorkerNodeWriter writer{pool, EXTENT_BYTES, extents.source()};

    auto const before = make_leaf_node_with_value_size(512, 1);
    auto const before_at = writer.append(*before);
    auto const oversized = make_leaf_node_with_value_size(4 * EXTENT_BYTES, 2);
    auto const oversized_at = writer.append(*oversized);
    auto const after = make_leaf_node_with_value_size(512, 3);
    auto const after_at = writer.append(*after);
    writer.flush();

    EXPECT_EQ(after_at.id, before_at.id);
    EXPECT_EQ(after_at.offset, before_at.offset + before->get_disk_size());
    // The extent starts where its first node landed, so the bespoke
    // reservation must begin past the whole of it
    EXPECT_GE(oversized_at.offset, before_at.offset + EXTENT_BYTES);

    EXPECT_EQ(read_node_at(pool, before_at)->value(), before->value());
    EXPECT_EQ(read_node_at(pool, oversized_at)->value(), oversized->value());
    EXPECT_EQ(read_node_at(pool, after_at)->value(), after->value());
}

TEST(ParallelUpsertContext, concurrent_reservations_never_exceed_a_chunk)
{
    storage_pool pool(use_anonymous_inode_tag{});
    // One page of room per chunk, so every reservation is for a chunk's last
    // page and the two threads race for the same remainder every time. An
    // unguarded read-then-reserve loses that race and trips chunk_t::reserve's
    // capacity assert.
    auto const all = reserve_concurrently(pool, DISK_PAGE_SIZE);
    // One reservation per chunk by construction, so this phase cannot see two
    // in the same chunk; the next test is what pins disjointness
    EXPECT_EQ(check_placement(pool, all), 0u);
}

TEST(ParallelUpsertContext, concurrent_reservations_of_one_chunk_never_overlap)
{
    storage_pool pool(use_anonymous_inode_tag{});
    // Eight pages per chunk, so most reservations share a chunk with a
    // neighbour and the disjointness comparison actually runs
    auto const all = reserve_concurrently(pool, 8 * DISK_PAGE_SIZE);
    EXPECT_GT(check_placement(pool, all), 0u);
}
