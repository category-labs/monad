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

#include "pool_workloads.hpp"

#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/small_prng.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/mpt/config.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/db_metadata_context.hpp>
#include <category/mpt/detail/db_metadata.hpp>
#include <category/mpt/detail/space_counters.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/update.hpp>

#include <unistd.h>

#include <cstddef>
#include <cstdint>
#include <deque>
#include <filesystem>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

using namespace MONAD_MPT_NAMESPACE;
using namespace MONAD_MPT_NAMESPACE::detail;
using monad::test::FifoWorkload;
using monad::test::PoolState;

namespace monad::mpt::test
{
    struct DbAccessor
    {
        static UpdateAux &aux(Db &db)
        {
            return const_cast<UpdateAux &>(db.aux());
        }
    };
}

namespace
{
    space_delta delta(
        uint64_t const fast_written, uint64_t const slow_written,
        uint64_t const fast_superseded, uint64_t const slow_superseded)
    {
        return {
            .written = {.fast = fast_written, .slow = slow_written},
            .superseded = {.fast = fast_superseded, .slow = slow_superseded}};
    }

    monad::bytes32_t key(uint8_t const k)
    {
        monad::bytes32_t id{};
        id.bytes[0] = k;
        return id;
    }

    // mpt-only callers finalize a version after upserting it.
    void upsert_and_finalize(
        Db &db, uint64_t const versions, bool const can_write_to_fast = true)
    {
        monad::small_prng rng{1};
        monad::byte_string const value(64, 0xab);
        Node::SharedPtr root;
        for (uint64_t version = 0; version < versions; ++version) {
            std::vector<monad::byte_string> keys;
            std::vector<Update> updates;
            keys.reserve(100);
            updates.reserve(100);
            UpdateList ls;
            for (int i = 0; i < 100; ++i) {
                keys.push_back(
                    monad::test::random_key(rng, monad::test::BULK_PREFIX));
                updates.push_back(make_update(keys.back(), value));
                ls.push_front(updates.back());
            }
            root = db.upsert(
                std::move(root),
                std::move(ls),
                version,
                /*enable_compaction=*/true,
                can_write_to_fast);
            db.update_finalized_version(version);
        }
    }

    void expect_counters_match_walk(PoolState &state)
    {
        uint64_t const version = state.version - 1;
        auto const root = state.aux.metadata_ctx().get_root_offset_at_version(
            version, timeline_id::primary);
        auto const walked =
            walk_live_bytes(state.aux, root, version, timeline_id::primary);
        ASSERT_TRUE(walked.has_value());
        auto const counted = state.aux.live_bytes();
        ASSERT_TRUE(counted.has_value());
        EXPECT_EQ(counted->slow, walked->slow);
        EXPECT_EQ(counted->fast, walked->fast);
    }
}

TEST(SpaceCounters, apply_clamps_at_zero)
{
    list_bytes const live{.fast = 100, .slow = 50};
    auto const after = apply(live, delta(10, 0, 200, 60));
    EXPECT_EQ(after.fast, 0u);
    EXPECT_EQ(after.slow, 0u);
    auto const grown = apply(live, delta(10, 20, 5, 0));
    EXPECT_EQ(grown.fast, 105u);
    EXPECT_EQ(grown.slow, 70u);
}

TEST(SpaceCounters, add_accumulates_per_key)
{
    settlement_table table;
    table.add(key(1), 10, delta(1, 2, 3, 4));
    table.add(key(1), 10, delta(10, 20, 30, 40));
    table.add(key(2), 10, delta(5, 5, 5, 5));
    EXPECT_EQ(table.size(), 2u);
    auto const won = table.settle(10, key(1));
    ASSERT_TRUE(won.has_value());
    EXPECT_EQ(won->written.fast, 11u);
    EXPECT_EQ(won->written.slow, 22u);
    EXPECT_EQ(won->superseded.fast, 33u);
    EXPECT_EQ(won->superseded.slow, 44u);
}

TEST(SpaceCounters, settle_applies_winner_and_drops_losers)
{
    settlement_table table;
    table.add(key(1), 10, delta(1, 1, 0, 0));
    table.add(key(2), 10, delta(9, 9, 9, 9));
    auto const won = table.settle(10, key(1));
    ASSERT_TRUE(won.has_value());
    EXPECT_EQ(won->written.fast, 1u);
    EXPECT_EQ(won->superseded.slow, 0u);
    EXPECT_EQ(table.size(), 0u);
}

TEST(SpaceCounters, settle_keeps_later_versions)
{
    settlement_table table;
    table.add(key(1), 10, delta(1, 1, 0, 0));
    table.add(key(3), 11, delta(7, 7, 7, 7));
    (void)table.settle(10, key(1));
    EXPECT_EQ(table.size(), 1u);
    auto const later = table.settle(11, key(3));
    ASSERT_TRUE(later.has_value());
    EXPECT_EQ(later->written.slow, 7u);
}

TEST(SpaceCounters, settle_empty_winner_is_not_missing)
{
    settlement_table table;
    table.add(key(1), 10, space_delta{});
    EXPECT_TRUE(table.settle(10, key(1)).has_value());
}

TEST(SpaceCounters, settle_unknown_winner_drops_entries)
{
    settlement_table table;
    table.add(key(1), 9, delta(1, 1, 1, 1));
    table.add(key(2), 10, delta(2, 2, 2, 2));
    EXPECT_FALSE(table.settle(10, key(9)).has_value());
    EXPECT_EQ(table.size(), 0u);
}

struct SpaceCountersFast
    : public monad::test::FillDBWithChunksGTest<monad::test::PRESSURE_POOL>
{
};

struct SpaceCountersSlow
    : public monad::test::FillDBWithChunksGTest<monad::test::PRESSURE_POOL>
{
};

TEST_F(SpaceCountersFast, counts_match_walk_after_fast_writes)
{
    auto &s = *state();
    expect_counters_match_walk(s);
    FifoWorkload fifo{4, 4096, 50, 7};
    for (int i = 0; i < 200; ++i) {
        fifo.run_block(s);
    }
    expect_counters_match_walk(s);
}

TEST_F(SpaceCountersSlow, counts_match_walk_after_slow_bulk_load)
{
    auto &s = *state();
    monad::test::bulk_load_to(s, 0.3, 4096, /*can_write_to_fast=*/false);
    expect_counters_match_walk(s);
    FifoWorkload fifo{4, 4096, 50, 7};
    for (int i = 0; i < 100; ++i) {
        fifo.run_block(s);
    }
    expect_counters_match_walk(s);
}

struct SpaceCountersReopen
    : public monad::test::FillDBWithChunksGTest<monad::test::PRESSURE_POOL>
{
};

struct SpaceCountersMarker
    : public monad::test::FillDBWithChunksGTest<monad::test::PRESSURE_POOL>
{
};

struct SpaceCountersVersion
    : public monad::test::FillDBWithChunksGTest<monad::test::PRESSURE_POOL>
{
};

struct SpaceCountersRewind
    : public monad::test::FillDBWithChunksGTest<monad::test::PRESSURE_POOL>
{
};

namespace
{
    void run_fifo_blocks(PoolState &state, int const blocks)
    {
        FifoWorkload fifo{4, 4096, 50, 7};
        for (int i = 0; i < blocks; ++i) {
            fifo.run_block(state);
        }
    }

    void reopen(PoolState &state)
    {
        state.aux.init(state.io, monad::test::PRESSURE_POOL.history_len);
    }
}

TEST_F(SpaceCountersReopen, counters_survive_reopen)
{
    auto &s = *state();
    run_fifo_blocks(s, 100);
    auto const before = s.aux.live_bytes();
    ASSERT_TRUE(before.has_value());
    reopen(s);
    EXPECT_EQ(s.aux.live_bytes(), before);
}

TEST_F(SpaceCountersMarker, missing_marker_reads_unknown)
{
    auto &s = *state();
    run_fifo_blocks(s, 20);
    s.aux.metadata_ctx().invalidate_space_counters();
    reopen(s);
    EXPECT_FALSE(s.aux.live_bytes().has_value());
}

// An older binary upserts and finalizes without restamping the counters.
TEST_F(SpaceCountersVersion, stale_stamp_reads_unknown)
{
    auto &s = *state();
    run_fifo_blocks(s, 20);
    auto const live = s.aux.live_bytes();
    ASSERT_TRUE(live.has_value());
    s.aux.update_finalized_version(s.version - 1);
    s.aux.metadata_ctx().set_space_counters(*live, s.version - 3);
    reopen(s);
    EXPECT_FALSE(s.aux.live_bytes().has_value());
}

struct SpaceCountersCrash
    : public monad::test::FillDBWithChunksGTest<monad::test::PRESSURE_POOL>
{
};

// statesync upserts past the finalized version without a settlement key; a
// crash and the open-time rewind to the finalized version discard them.
TEST_F(SpaceCountersCrash, rewind_drops_counts_of_upserts_past_finalized)
{
    auto &s = *state();
    run_fifo_blocks(s, 20);
    uint64_t const finalized = s.version - 1;
    s.aux.update_finalized_version(finalized);
    ASSERT_TRUE(s.aux.live_bytes().has_value());
    run_fifo_blocks(s, 1);
    reopen(s);
    s.aux.rewind_to_version(finalized);
    EXPECT_FALSE(s.aux.live_bytes().has_value());
}

struct SpaceCountersSecondary
    : public monad::test::FillDBWithChunksGTest<monad::test::PRESSURE_POOL>
{
};

// The walk sees only the primary; the secondary's nodes would count as
// garbage that collection cannot free.
TEST_F(SpaceCountersSecondary, secondary_timeline_keeps_counters_unknown)
{
    auto &s = *state();
    run_fifo_blocks(s, 20);
    s.aux.activate_secondary_timeline();
    run_fifo_blocks(s, 5);
    s.aux.wait_for_space_walk_unit_testing_only();
    EXPECT_FALSE(s.aux.live_bytes().has_value());
    EXPECT_FALSE(s.aux.metadata_ctx().space_counters().has_value());
    s.aux.deactivate_secondary_timeline();
}

// The bft disk gauges read these stats through a read-only handle, also
// after the writer has used its last free chunk.
TEST(SpaceCountersDb, stats_with_no_free_chunks_report_zero_free)
{
    Db db{
        std::make_unique<monad::test::StateMachineAlwaysMerkle>(),
        OnDiskDbConfig{.chunk_capacity = 24}};
    auto &meta = monad::mpt::test::DbAccessor::aux(db).metadata_ctx();
    while (auto const *const ci = meta.main()->free_list_begin()) {
        uint32_t const idx = ci->index(meta.main());
        meta.remove(idx);
        meta.append(DbMetadataContext::chunk_list::fast, idx);
    }
    EXPECT_EQ(db.get_storage_stats().free_chunk_bytes, 0u);
}

TEST(SpaceCountersDb, finalizing_after_the_upsert_keeps_counters_known)
{
    auto const name = std::filesystem::temp_directory_path() /
                      ("space_counters_finalize_" + std::to_string(::getpid()));
    auto const config = [&](bool const append) {
        return OnDiskDbConfig{
            .append = append, .dbname_path = name, .chunk_capacity = 24};
    };
    {
        Db db{
            std::make_unique<monad::test::StateMachineAlwaysMerkle>(),
            config(false)};
        upsert_and_finalize(db, 3);
        EXPECT_TRUE(db.get_storage_stats().live_bytes_known);
    }
    {
        Db const db{
            std::make_unique<monad::test::StateMachineAlwaysMerkle>(),
            config(true)};
        EXPECT_TRUE(db.get_storage_stats().live_bytes_known);
    }
    std::filesystem::remove(name);
}

TEST_F(SpaceCountersRewind, rewind_below_counters_invalidates_them)
{
    auto &s = *state();
    run_fifo_blocks(s, 20);
    ASSERT_TRUE(s.aux.metadata_ctx().space_counters().has_value());
    s.aux.rewind_to_version(s.version - 5);
    EXPECT_FALSE(s.aux.metadata_ctx().space_counters().has_value());
    EXPECT_FALSE(s.aux.live_bytes().has_value());
}

struct SpaceCountersRestart
    : public monad::test::FillDBWithChunksGTest<monad::test::PRESSURE_POOL>
{
};

// The open-time rewind to the latest finalized version is where the
// counters were persisted, so a normal restart keeps them.
TEST_F(SpaceCountersRestart, rewind_to_counters_version_keeps_them)
{
    auto &s = *state();
    run_fifo_blocks(s, 20);
    uint64_t const finalized = s.version - 1;
    s.aux.metadata_ctx().set_latest_finalized_version(finalized);
    auto const live = s.aux.live_bytes();
    ASSERT_TRUE(live.has_value());
    s.aux.metadata_ctx().set_space_counters(*live, finalized);
    s.aux.rewind_to_version(finalized);
    EXPECT_EQ(s.aux.live_bytes(), live);
    ASSERT_TRUE(s.aux.metadata_ctx().space_counters().has_value());
}

struct SpaceCountersWalk
    : public monad::test::FillDBWithChunksGTest<monad::test::PRESSURE_POOL>
{
};

struct SpaceCountersWalkRetry
    : public monad::test::FillDBWithChunksGTest<monad::test::PRESSURE_POOL>
{
};

TEST_F(SpaceCountersWalk, walk_fills_unknown_counters)
{
    auto &s = *state();
    monad::test::bulk_load_to(s, 0.2, 4096, /*can_write_to_fast=*/false);
    run_fifo_blocks(s, 20);
    s.aux.metadata_ctx().invalidate_space_counters();
    reopen(s);
    ASSERT_FALSE(s.aux.live_bytes().has_value());
    run_fifo_blocks(s, 50);
    s.aux.wait_for_space_walk_unit_testing_only();
    expect_counters_match_walk(s);
    EXPECT_TRUE(s.aux.metadata_ctx().space_counters().has_value());
}

TEST_F(SpaceCountersWalkRetry, walk_restarts_when_version_expires)
{
    auto &s = *state();
    run_fifo_blocks(s, 20);
    s.aux.metadata_ctx().invalidate_space_counters();
    reopen(s);
    s.aux.pause_space_walk_unit_testing_only(true);
    // Longer than the 64-version history, so the walk's version expires.
    run_fifo_blocks(s, 80);
    s.aux.pause_space_walk_unit_testing_only(false);
    s.aux.wait_for_space_walk_unit_testing_only();
    expect_counters_match_walk(s);
}

struct SpaceCountersCompaction
    : public monad::test::FillDBWithChunksGTest<monad::test::PRESSURE_POOL>
{
};

TEST_F(SpaceCountersCompaction, counts_match_walk_across_compaction)
{
    auto &s = *state();
    monad::test::bulk_load_to(s, 0.3, 4096, /*can_write_to_fast=*/false);
    FifoWorkload fifo{4, 4096, 3000, 7};
    bool copied_to_slow = false;
    for (int i = 0; i < 6000 && !copied_to_slow; ++i) {
        fifo.run_block(s);
        copied_to_slow = s.aux.last_upsert_stats().compacted_bytes_in_fast > 0;
    }
    ASSERT_TRUE(copied_to_slow);
    s.aux.slow_collection_override_unit_testing_only(2);
    for (int i = 0; i < 300; ++i) {
        fifo.run_block(s);
    }
    s.aux.slow_collection_override_unit_testing_only(std::nullopt);
    expect_counters_match_walk(s);
}

namespace
{
    // Each block upserts a key holding a subtrie of `slots` keys and erases
    // the key upserted `lifetime` blocks earlier, which drops its subtrie
    // whole.
    class SubtrieWorkload
    {
        size_t slots_;
        size_t lifetime_;
        monad::byte_string value_;
        monad::small_prng rng_{3};
        std::deque<monad::byte_string> live_;

    public:
        SubtrieWorkload(size_t const slots, size_t const lifetime)
            : slots_{slots}
            , lifetime_{lifetime}
            , value_(64, 0xef)
        {
        }

        void run_block(PoolState &state)
        {
            std::vector<monad::byte_string> slot_keys;
            std::vector<Update> slot_updates;
            slot_keys.reserve(slots_);
            slot_updates.reserve(slots_);
            UpdateList slots;
            for (size_t i = 0; i < slots_; ++i) {
                slot_keys.push_back(
                    monad::test::random_key(rng_, monad::test::BULK_PREFIX));
                slot_updates.push_back(make_update(slot_keys.back(), value_));
                slots.push_front(slot_updates.back());
            }
            monad::byte_string const key =
                monad::test::random_key(rng_, monad::test::FIFO_PREFIX);
            std::optional<monad::byte_string> expired;
            if (live_.size() == lifetime_) {
                expired = std::move(live_.front());
                live_.pop_front();
            }
            std::vector<Update> updates;
            updates.reserve(2);
            UpdateList ls;
            updates.push_back(
                make_update(key, value_, false, std::move(slots)));
            ls.push_front(updates.back());
            if (expired.has_value()) {
                updates.push_back(make_erase(*expired));
                ls.push_front(updates.back());
            }
            monad::test::pool_upsert(
                state,
                std::move(ls),
                state.version++,
                /*compaction=*/true,
                /*can_write_to_fast=*/true);
            live_.push_back(key);
        }
    };
}

struct SpaceCountersRecount
    : public monad::test::FillDBWithChunksGTest<monad::test::PRESSURE_POOL>
{
};

TEST_F(SpaceCountersRecount, recount_corrects_erased_subtries)
{
    auto &s = *state();
    SubtrieWorkload subtries{20, 4};
    for (int i = 0; i < 30; ++i) {
        subtries.run_block(s);
    }
    uint64_t const version = s.version - 1;
    auto const walked = walk_live_bytes(
        s.aux,
        s.aux.metadata_ctx().get_root_offset_at_version(
            version, timeline_id::primary),
        version,
        timeline_id::primary);
    ASSERT_TRUE(walked.has_value());
    auto const counted = s.aux.live_bytes();
    ASSERT_TRUE(counted.has_value());
    EXPECT_GT(counted->fast + counted->slow, walked->fast + walked->slow);

    s.aux.space_walk_interval_unit_testing_only(1);
    run_fifo_blocks(s, 3);
    s.aux.wait_for_space_walk_unit_testing_only();
    expect_counters_match_walk(s);
}

struct SpaceCountersLostSettlement
    : public monad::test::FillDBWithChunksGTest<monad::test::PRESSURE_POOL>
{
};

// An open that keeps a committed proposal has none of its sums.
TEST_F(SpaceCountersLostSettlement, finalizing_a_proposal_from_before_open)
{
    auto &s = *state();
    run_fifo_blocks(s, 20);
    s.aux.update_finalized_version(s.version - 1);
    s.aux.set_settlement_key(key(1));
    run_fifo_blocks(s, 1);
    s.aux.set_settlement_key(std::nullopt);
    reopen(s);
    ASSERT_TRUE(s.aux.live_bytes().has_value());
    s.aux.settle_space_counters(s.version - 1, key(1));
    s.aux.update_finalized_version(s.version - 1);
    EXPECT_FALSE(s.aux.live_bytes().has_value());
    EXPECT_FALSE(s.aux.metadata_ctx().valid_space_counters().has_value());
    s.aux.wait_for_space_walk_unit_testing_only();
    expect_counters_match_walk(s);
}

struct SpaceCountersWalkCancel
    : public monad::test::FillDBWithChunksGTest<monad::test::PRESSURE_POOL>
{
};

TEST_F(SpaceCountersWalkCancel, invalidation_drops_a_running_walk)
{
    auto &s = *state();
    run_fifo_blocks(s, 20);
    s.aux.metadata_ctx().invalidate_space_counters();
    reopen(s);
    s.aux.pause_space_walk_unit_testing_only(true);
    run_fifo_blocks(s, 1);
    s.aux.activate_secondary_timeline();
    s.aux.pause_space_walk_unit_testing_only(false);
    s.aux.wait_for_space_walk_unit_testing_only();
    EXPECT_FALSE(s.aux.live_bytes().has_value());
    EXPECT_FALSE(s.aux.metadata_ctx().space_counters().has_value());
    s.aux.deactivate_secondary_timeline();
}

struct SpaceCountersTorn
    : public monad::test::FillDBWithChunksGTest<monad::test::PRESSURE_POOL>
{
};

// What a reader sees of a writer that died mid-update, or that moved a
// list's end chunk to another list while it was reading.
TEST_F(SpaceCountersTorn, torn_metadata_reads_unknown)
{
    auto &s = *state();
    run_fifo_blocks(s, 20);
    auto &meta = s.aux.metadata_ctx();
    auto *const m = const_cast<db_metadata *>(meta.main());

    auto const counters = meta.space_counters();
    ASSERT_TRUE(counters.has_value());
    m->space_counters.sequence |= 1;
    EXPECT_FALSE(meta.space_counters().has_value());
    meta.set_space_counters(counters->first, counters->second);
    EXPECT_EQ(meta.space_counters(), counters);

    using list = UpdateAux::chunk_list;
    for (auto const l : {list::free, list::fast, list::slow}) {
        EXPECT_EQ(
            meta.list_chunk_count(l).value_or(UINT32_MAX), s.aux.num_chunks(l));
    }
    uint32_t const free_begin = m->free_list.begin;
    m->free_list.begin = m->fast_list.begin;
    EXPECT_FALSE(meta.list_chunk_count(list::free).has_value());
    m->free_list.begin = free_begin;
}
