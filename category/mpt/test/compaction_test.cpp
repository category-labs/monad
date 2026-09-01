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
#include "test_fixtures_gtest.hpp"

#include <category/async/config.hpp>
#include <category/async/detail/scope_polyfill.hpp>
#include <category/async/util.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/mpt/config.hpp>
#include <category/mpt/db_stats_shm.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/update.hpp>

#include <cstddef>
#include <filesystem>
#include <iostream>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

#include <unistd.h>

using namespace MONAD_ASYNC_NAMESPACE;
using namespace MONAD_MPT_NAMESPACE;
using namespace monad::literals;

static constexpr size_t CHUNKS_TO_FILL = 8;

struct CompactionTest
    : public monad::test::FillDBWithChunksGTest<
          monad::test::FillDBWithChunksConfig{.chunks_to_fill = CHUNKS_TO_FILL}>
{
};

TEST_F(CompactionTest, first_chunk_is_compacted)
{
    std::vector<Update> updates;
    auto const fast_list_ids = state()->fast_list_ids();
    for (auto const &i : state()->keys) {
        if (i.second > fast_list_ids[0].first) {
            break;
        }
        updates.push_back(make_update(i.first, UpdateList{}));
    }
    std::cout << "Erasing the first " << updates.size()
              << " inserted keys, which should enable the whole of the "
                 "first block to be compacted away."
              << std::endl;
    UpdateList update_ls;
    for (auto &i : updates) {
        update_ls.push_front(i);
    }
    state()->root = state()->aux.do_update(
        std::move(state()->root),
        state()->sm,
        std::move(update_ls),
        state()->version++,
        /*compaction=*/false,
        /*can_write_to_fast=*/true,
        /*write_root=*/true,
        timeline_id::primary);
    std::cout << "\nBefore compaction:";
    state()->print(std::cout);
    // TODO DO COMPACTION
    // TODO CHECK POOL'S FIRST CHUNK WAS DEFINITELY RELEASED
}

TEST_F(CompactionTest, last_upsert_stats_isolates_the_latest_upsert)
{
    auto &aux = state()->aux;
    // The fixture has already run many upserts, so the lifetime totals start
    // well above zero, which is what makes the isolation checks meaningful.
    ASSERT_GT(aux.stats_snapshot().nodes_created_or_updated, 0u);

    auto const erase_keys = [&](size_t const first, size_t const count) {
        std::vector<Update> updates;
        updates.reserve(count);
        for (size_t i = 0; i < count; ++i) {
            updates.push_back(
                make_update(state()->keys[first + i].first, UpdateList{}));
        }
        UpdateList ls;
        for (auto &update : updates) {
            ls.push_front(update);
        }
        // compaction=false also pins that the per-upsert delta advances on
        // upserts that never reach the compaction code.
        state()->root = aux.do_update(
            std::move(state()->root),
            state()->sm,
            std::move(ls),
            state()->version++,
            /*compaction=*/false,
            /*can_write_to_fast=*/true,
            /*write_root=*/true,
            timeline_id::primary);
    };

    auto const lifetime_before = aux.stats_snapshot();
    erase_keys(0, 4);
    auto const lifetime_first = aux.stats_snapshot();
    auto const delta_first = aux.last_upsert_stats();
    erase_keys(4, 4);
    auto const lifetime_second = aux.stats_snapshot();
    auto const delta_second = aux.last_upsert_stats();

    // Each delta is exactly the lifetime growth across its own upsert.
    EXPECT_EQ(
        lifetime_first.nodes_created_or_updated -
            lifetime_before.nodes_created_or_updated,
        delta_first.nodes_created_or_updated);
    EXPECT_EQ(
        lifetime_second.nodes_created_or_updated -
            lifetime_first.nodes_created_or_updated,
        delta_second.nodes_created_or_updated);

    // The lifetime totals only ever grow, and a delta stays strictly below
    // them: a reintroduced reset breaks the first property, handing a consumer
    // the lifetime totals instead of the delta breaks the second.
    EXPECT_GE(
        lifetime_second.nodes_created_or_updated,
        lifetime_first.nodes_created_or_updated);
    EXPECT_GT(delta_second.nodes_created_or_updated, 0u);
    EXPECT_LT(
        delta_second.nodes_created_or_updated,
        lifetime_second.nodes_created_or_updated);
}

TEST_F(CompactionTest, an_upsert_publishes_lifetime_totals_to_the_sidecar)
{
    auto const path =
        MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
        ("monad_db_stats_compaction_" + std::to_string(::getpid()));
    std::filesystem::remove(path);
    auto const remove_sidecar = monad::make_scope_exit(
        [&]() noexcept { std::filesystem::remove(path); });

    auto publisher = DbStatsPublisher::create(path);
    ASSERT_TRUE(publisher.has_value());
    auto &aux = state()->aux;
    aux.set_stats_publisher(&publisher.value());
    // The fixture's aux outlives this test body; the publisher does not.
    auto const clear_publisher = monad::make_scope_exit(
        [&]() noexcept { aux.set_stats_publisher(nullptr); });

    auto erase = make_update(state()->keys[0].first, UpdateList{});
    UpdateList ls;
    ls.push_front(erase);
    // compaction=false: the sidecar has to be written by every upsert, not
    // only by those that reach the compaction code.
    state()->root = aux.do_update(
        std::move(state()->root),
        state()->sm,
        std::move(ls),
        state()->version++,
        /*compaction=*/false,
        /*can_write_to_fast=*/true,
        /*write_root=*/true,
        timeline_id::primary);

    auto const reader = DbStatsReader::open(path);
    ASSERT_TRUE(reader.has_value());
    auto const published = reader->read_update_stats();
    ASSERT_TRUE(published.has_value());
    // Lifetime totals rather than the per-upsert delta: a scraper sampling on
    // its own schedule needs counters that outlive the upsert that produced
    // them.
    EXPECT_EQ(
        published->nodes_created_or_updated,
        aux.stats_snapshot().nodes_created_or_updated);
    EXPECT_GT(
        published->nodes_created_or_updated,
        aux.last_upsert_stats().nodes_created_or_updated);
}
