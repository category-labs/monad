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

#include <category/async/detail/scope_polyfill.hpp>
#include <category/core/assert.h>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/mpt/detail/db_metadata.hpp>

#include <gtest/gtest.h>

#include <atomic>
#include <chrono>
#include <cstddef>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <ostream>
#include <stop_token>
#include <thread>
#include <utility>

TEST(db_metadata, DISABLED_copy)
{
#if MONAD_CONTEXT_HAVE_TSAN
    return; // This test explicitly relies on racy memory copying
#endif
    monad::mpt::detail::db_metadata *metadata[3];
    metadata[0] = (monad::mpt::detail::db_metadata *)calloc(
        1, sizeof(monad::mpt::detail::db_metadata));
    metadata[1] = (monad::mpt::detail::db_metadata *)calloc(
        1, sizeof(monad::mpt::detail::db_metadata));
    metadata[2] = (monad::mpt::detail::db_metadata *)calloc(
        1, sizeof(monad::mpt::detail::db_metadata));
    auto const unmetadata = monad::make_scope_exit([&]() noexcept {
        free(metadata[0]);
        free(metadata[1]);
        free(metadata[2]);
    });
    std::atomic<int> latch{-1};
    std::jthread thread([&](std::stop_token tok) {
        while (!tok.stop_requested()) {
            int expected = 0;
            while (!latch.compare_exchange_strong(
                       expected, 1, std::memory_order_acq_rel) &&
                   !tok.stop_requested()) {
                std::this_thread::yield();
                expected = 0;
            }
            db_copy(
                metadata[0],
                metadata[1],
                sizeof(monad::mpt::detail::db_metadata));
            MONAD_ASSERT(
                !metadata[0]->is_dirty().load(std::memory_order_acquire));
            latch.store(-1, std::memory_order_release);
        }
    });
    metadata[1]->chunk_info_count = 6;
    metadata[1]->capacity_in_free_list = 6;
    unsigned count = 0;
    auto const begin = std::chrono::steady_clock::now();
    while (std::chrono::steady_clock::now() - begin <
           std::chrono::seconds((count == 0) ? 60 : 5)) {
        if (metadata[0]->is_dirty().load(std::memory_order_acquire)) {
            EXPECT_FALSE(true);
        }
        metadata[0]->chunk_info_count = 5;
        metadata[0]->capacity_in_free_list = 5;
        latch.store(0, std::memory_order_release);
        do {
            memcpy((void *)metadata[2], metadata[0], 32);
            // If first half copied but not yet second half, dirty bit must be
            // set
            if (metadata[2]->chunk_info_count != 5 &&
                metadata[2]->capacity_in_free_list == 5) {
                if (!metadata[2]->is_dirty().load(std::memory_order_acquire)) {
                    EXPECT_TRUE(metadata[2]->is_dirty().load(
                        std::memory_order_acquire));
                }
                count++;
            }
        }
        while (latch.load(std::memory_order_acquire) != -1);
    }
    thread.request_stop();
    thread.join();
    EXPECT_GT(count, 0);
    std::cout << count << std::endl;
}

// -------------------------------------------------------------------
// secondary_timeline_header_t layout and semantics
// -------------------------------------------------------------------

TEST(db_metadata, total_size)
{
    // Both rings now use the same ring-header type. The total metadata size
    // is dominated by the cnv_chunks lists in each ring (SIZE_=32).
    EXPECT_EQ(sizeof(monad::mpt::detail::db_metadata), 4480u);
}

TEST(db_metadata, ring_b_layout_matches_ring_a)
{
    using md = monad::mpt::detail::db_metadata;
    // Both physical rings use the same header type, so promote is a mere
    // label flip — no structural asymmetry between the rings.
    EXPECT_EQ(
        sizeof(md::root_offsets_ring_t),
        sizeof(std::declval<md &>().root_offsets));
    EXPECT_EQ(
        sizeof(md::root_offsets_ring_t),
        sizeof(std::declval<md &>().secondary_timeline));

    // Layout order: root_offsets → ... → secondary_timeline →
    // primary_ring_idx → secondary_timeline_active_ → reserved_timeline_[6]
    // → shrink_grow_seq_ → pending_shrink_grow → future_variables_unused.
    auto const offset_secondary = offsetof(md, secondary_timeline);
    auto const offset_primary_ring_idx = offsetof(md, primary_ring_idx);
    auto const offset_active = offsetof(md, secondary_timeline_active_);
    auto const offset_reserved = offsetof(md, reserved_timeline_);
    auto const offset_seq = offsetof(md, shrink_grow_seq_);
    auto const offset_pending = offsetof(md, pending_shrink_grow);
    auto const offset_future = offsetof(md, future_variables_unused);
    EXPECT_EQ(
        offset_primary_ring_idx - offset_secondary,
        sizeof(md::root_offsets_ring_t));
    EXPECT_EQ(offset_active, offset_primary_ring_idx + 1);
    EXPECT_EQ(offset_reserved, offset_active + 1);
    EXPECT_EQ(offset_seq, offset_reserved + 6);
    EXPECT_EQ(offset_pending, offset_seq + 8);
    EXPECT_EQ(
        offset_future, offset_pending + sizeof(md::pending_shrink_grow_t));
}

TEST(db_metadata, role_bytes_zero_initialized)
{
    // A freshly created (zeroed) db_metadata has ring_a as primary and
    // the secondary role inactive. Backward-compat: older DBs opened by
    // new code see the secondary as inactive and ring_a as primary.
    auto *m = (monad::mpt::detail::db_metadata *)calloc(
        1, sizeof(monad::mpt::detail::db_metadata));
    auto const cleanup = monad::make_scope_exit([&]() noexcept { free(m); });

    EXPECT_EQ(m->secondary_timeline.version_lower_bound_, 0u);
    EXPECT_EQ(m->secondary_timeline.next_version_, 0u);
    EXPECT_EQ(m->primary_ring_idx, 0u);
    EXPECT_EQ(m->secondary_timeline_active_, 0u);
}

TEST(db_metadata, secondary_timeline_header_read_write)
{
    using md = monad::mpt::detail::db_metadata;
    // Verify fields can be set and read back through the metadata struct.
    auto *m = static_cast<md *>(calloc(1, sizeof(md)));
    auto const cleanup = monad::make_scope_exit([&]() noexcept { free(m); });

    m->secondary_timeline.version_lower_bound_ = 42;
    m->secondary_timeline.next_version_ = 43;
    m->secondary_timeline_active_ = 1;
    m->primary_ring_idx = 1;

    EXPECT_EQ(m->secondary_timeline.version_lower_bound_, 42u);
    EXPECT_EQ(m->secondary_timeline.next_version_, 43u);
    EXPECT_EQ(m->secondary_timeline_active_, 1u);
    EXPECT_EQ(m->primary_ring_idx, 1u);
}

TEST(db_metadata, secondary_timeline_header_survives_metadata_copy)
{
    using md = monad::mpt::detail::db_metadata;
    // The dual-copy crash-safety mechanism uses raw memcpy between the two
    // metadata copies. The secondary header and top-level role bytes must
    // survive this.
    auto *src = static_cast<md *>(calloc(1, sizeof(md)));
    auto const cleanup_src =
        monad::make_scope_exit([&]() noexcept { free(src); });
    src->secondary_timeline.version_lower_bound_ = 100;
    src->secondary_timeline.next_version_ = 200;
    src->secondary_timeline_active_ = 1;
    src->primary_ring_idx = 1;

    auto *dst = static_cast<md *>(calloc(1, sizeof(md)));
    auto const cleanup_dst =
        monad::make_scope_exit([&]() noexcept { free(dst); });
    std::memcpy(dst, src, sizeof(md));

    EXPECT_EQ(dst->secondary_timeline.version_lower_bound_, 100u);
    EXPECT_EQ(dst->secondary_timeline.next_version_, 200u);
    EXPECT_EQ(dst->secondary_timeline_active_, 1u);
    EXPECT_EQ(dst->primary_ring_idx, 1u);
}

TEST(db_metadata, secondary_timeline_does_not_overlap_consensus_fields)
{
    using md = monad::mpt::detail::db_metadata;
    // The secondary header must not overlap with consensus fields that
    // precede it.
    auto const end_of_proposed_block_id =
        offsetof(md, latest_proposed_block_id) +
        sizeof(std::declval<md &>().latest_proposed_block_id);
    auto const start_of_secondary = offsetof(md, secondary_timeline);
    EXPECT_GE(start_of_secondary, end_of_proposed_block_id);
}

// db_copy zeroes next_version_ on dest before the bulk memcpy, then atomically
// restores both root_offsets.next_version_ and secondary_timeline.next_version_
// after, so concurrent readers never observe a half-copied ring with a stale
// advance cursor. Verify the secondary cursor is preserved.
TEST(db_metadata, db_copy_preserves_secondary_next_version)
{
    using md = monad::mpt::detail::db_metadata;
    auto *src = static_cast<md *>(calloc(1, sizeof(md)));
    auto *dst = static_cast<md *>(calloc(1, sizeof(md)));
    auto const cleanup = monad::make_scope_exit([&]() noexcept {
        free(src);
        free(dst);
    });

    src->secondary_timeline.version_lower_bound_ = 7;
    src->secondary_timeline.next_version_ = 42;
    src->secondary_timeline_active_ = 1;
    src->primary_ring_idx = 1;

    monad::mpt::detail::db_copy(dst, src, sizeof(md));

    EXPECT_EQ(dst->secondary_timeline.version_lower_bound_, 7u);
    EXPECT_EQ(dst->secondary_timeline.next_version_, 42u);
    EXPECT_EQ(dst->secondary_timeline_active_, 1u);
    EXPECT_EQ(dst->primary_ring_idx, 1u);
}
