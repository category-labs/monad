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
#include <category/async/detail/scope_polyfill.hpp>
#include <category/async/io.hpp>
#include <category/async/storage_pool.hpp>
#include <category/async/util.hpp>
#include <category/core/assert.h>
#include <category/core/detail/start_lifetime_as_polyfill.hpp>
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>
#include <category/mpt/db_metadata_context.hpp>
#include <category/mpt/detail/db_metadata.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/state_machine_kind.hpp>
#include <category/mpt/test/db_metadata_test_access.hpp>
#include <category/mpt/test/grow_database_test_util.hpp>
#include <category/mpt/test/legacy_metadata.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/util.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <atomic>
#include <csignal>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <memory>
#include <ostream>
#include <stop_token>
#include <string>
#include <thread>
#include <vector>

#include <stdlib.h>
#include <unistd.h>

using namespace std::chrono_literals;
using namespace monad::mpt;

namespace
{
    constexpr uint64_t AUX_TEST_HISTORY_LENGTH = 1000;

    // Helper: set up a writable UpdateAux on a background thread, run a
    // callback, then tear down.  The callback receives the aux reference
    // and runs on the caller's thread after init completes.
    template <typename F>
    void with_rw_aux(F &&fn)
    {
        monad::async::storage_pool pool(
            monad::async::use_anonymous_inode_tag{});
        UpdateAux aux{};
        std::atomic<bool> io_set = false;
        std::atomic<bool> done = false;
        std::jthread const rw_asyncio([&](std::stop_token) {
            monad::io::Ring ring1;
            monad::io::Ring ring2;
            monad::io::Buffers testbuf =
                monad::io::make_buffers_for_segregated_read_write(
                    ring1,
                    ring2,
                    2,
                    4,
                    monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                    monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
            monad::async::AsyncIO testio(pool, testbuf);
            aux.init(testio, AUX_TEST_HISTORY_LENGTH);
            io_set = true;

            while (!done.load(std::memory_order_acquire)) {
                std::this_thread::sleep_for(10ms);
            }
            // Re-init tears down the old metadata_ctx before testio
            // goes out of scope on this thread's stack.
            aux.~UpdateAux();
            new (&aux) UpdateAux{};
        });
        while (!io_set) {
            std::this_thread::yield();
        }
        fn(aux);
        done.store(true, std::memory_order_release);
    }
}

TEST(update_aux_test, reader_dirty_aborts)
{
    monad::async::storage_pool pool(monad::async::use_anonymous_inode_tag{});

    // All this threading nonsense is because we can't have two AsyncIO
    // instances on the same thread.

    std::unique_ptr<monad::mpt::UpdateAux> aux_writer;
    std::atomic<bool> io_set = false;
    std::jthread const rw_asyncio([&](std::stop_token token) {
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers testbuf =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testbuf);
        aux_writer = std::make_unique<monad::mpt::UpdateAux>(
            testio, AUX_TEST_HISTORY_LENGTH);
        io_set = true;

        while (!token.stop_requested()) {
            std::this_thread::sleep_for(10ms);
        }
        // Destroy before local AsyncIO/Buffers/Rings go out of scope
        aux_writer.reset();
    });
    while (!io_set) {
        std::this_thread::yield();
    }

    // Set both bits dirty
    aux_writer->metadata_ctx().modify_metadata(
        [](monad::mpt::detail::db_metadata *m) {
            m->is_dirty().store(1, std::memory_order_release);
        });

    ASSERT_TRUE(const_cast<monad::mpt::detail::db_metadata *>(
                    aux_writer->metadata_ctx().main())
                    ->is_dirty());

    monad::io::Ring ring;
    monad::io::Buffers testrobuf = monad::io::make_buffers_for_read_only(
        ring, 2, monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE);
    auto pool_ro = pool.clone_as_read_only();
    monad::async::AsyncIO testio(pool_ro, testrobuf);

    // RO open should abort when dirty bits are set and never clear.
    ASSERT_DEATH(
        ({ monad::mpt::DbMetadataContext{testio}; }),
        "DB metadata was closed dirty, but not opened for healing");

    // Clear the dirty bits (simulates writer finishing its update).
    aux_writer->metadata_ctx().modify_metadata(
        [](monad::mpt::detail::db_metadata *m) {
            m->is_dirty().store(0, std::memory_order_release);
        });

    // RO open should now succeed since dirty bits are clear.
    EXPECT_NO_THROW(({ monad::mpt::DbMetadataContext{testio}; }));
}

TEST(update_aux_test, root_offsets_fast_slow)
{
    testing::FLAGS_gtest_death_test_style = "threadsafe";

    monad::async::storage_pool pool(monad::async::use_anonymous_inode_tag{});
    monad::io::Ring ring1;
    monad::io::Ring ring2;
    monad::io::Buffers testbuf =
        monad::io::make_buffers_for_segregated_read_write(
            ring1,
            ring2,
            2,
            4,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
    monad::async::AsyncIO testio(pool, testbuf);
    {
        monad::mpt::UpdateAux aux_writer{testio, AUX_TEST_HISTORY_LENGTH};

        // Root offset at 0, fast list offset at 50. This is correct
        auto const start_offset =
            aux_writer.node_writer_fast->sender().offset();
        (void)pool
            .chunk(monad::async::storage_pool::chunk_type::seq, start_offset.id)
            .write_fd(50);
        auto const end_offset =
            aux_writer.node_writer_fast->sender().offset().add_to_offset(50);
        aux_writer.metadata_ctx().append_root_offset(
            start_offset, timeline_id::primary);
        aux_writer.metadata_ctx().advance_db_offsets_to(
            end_offset, aux_writer.node_writer_slow->sender().offset());
    }
    {
        // verify construction succeeds
        monad::mpt::UpdateAux aux_writer{testio, AUX_TEST_HISTORY_LENGTH};
        EXPECT_EQ(aux_writer.metadata_ctx().root_offsets().max_version(), 0);

        // Write version 1. However, append the new root offset without
        // advancing fast list
        auto const start_offset =
            aux_writer.node_writer_fast->sender().offset();
        (void)pool
            .chunk(monad::async::storage_pool::chunk_type::seq, start_offset.id)
            .write_fd(100);
        auto const end_offset =
            aux_writer.node_writer_fast->sender().offset().add_to_offset(100);
        aux_writer.metadata_ctx().append_root_offset(
            end_offset, timeline_id::primary);
    }

    { // Fail to reopen upon calling rewind_to_match_offsets()
        EXPECT_EXIT(
            ({ monad::mpt::UpdateAux{testio, AUX_TEST_HISTORY_LENGTH}; }),
            ::testing::KilledBySignal(SIGABRT),
            "Detected corruption");
    }
}

TEST(update_aux_test, configurable_root_offset_chunks)
{
    std::filesystem::path const filename{
        MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
        "monad_update_aux_test_XXXXXX"};
    int const fd = ::mkstemp((char *)filename.native().data());
    MONAD_ASSERT(fd != -1);
    MONAD_ASSERT(-1 != ::ftruncate(fd, 8UL << 30)); // 8GB

    monad::io::Ring ring1;
    monad::io::Ring ring2;
    monad::io::Buffers testbuf =
        monad::io::make_buffers_for_segregated_read_write(
            ring1,
            ring2,
            2,
            4,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
    // Default chunk capacity: the root offset ring capacity asserted below
    // is derived from it.
    monad::async::storage_pool::creation_flags flags;
    flags.num_cnv_chunks = 5;
    {
        // Create storage pool with 5 cnv chunks: 1 for metadata, 4 for
        // ring_a at init (ring_b has 0 chunks until secondary activates).
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::truncate, flags);
        EXPECT_EQ(pool.chunks(monad::async::storage_pool::cnv), 5);

        monad::async::AsyncIO testio(pool, testbuf);
        monad::mpt::UpdateAux const aux(testio);

        // Verify that exactly 4 chunks were allocated to hold two copies of
        // root offsets, since chunk 0 is used for metadata
        EXPECT_EQ(aux.metadata_ctx().main()->root_offsets.cnv_chunks_len(), 4);
        EXPECT_EQ(
            aux.metadata_ctx().main()->secondary_timeline.cnv_chunks_len(), 0);
        EXPECT_EQ(aux.metadata_ctx().root_offsets().capacity(), 2ULL << 25);
    }
    {
        // reopen storage_pool
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::open_existing, flags);
        EXPECT_EQ(pool.chunks(monad::async::storage_pool::cnv), 5);
        monad::async::AsyncIO testio(pool, testbuf);
        monad::mpt::UpdateAux const aux(testio);
        EXPECT_EQ(aux.metadata_ctx().main()->root_offsets.cnv_chunks_len(), 4);
        EXPECT_EQ(
            aux.metadata_ctx().main()->secondary_timeline.cnv_chunks_len(), 0);
        EXPECT_EQ(aux.metadata_ctx().root_offsets().capacity(), 2ULL << 25);
    }
    remove(filename);
}

// A DB created before the num_cnv_chunks footer field existed stores 0 there.
// The pool must treat that as the legacy default of 3 conventional chunks
// (1 for metadata + 2 for ring_a), not as a raw 0 that underflows
// ring_max_chunks_() to UINT32_MAX and aborts the mmap on reopen.
// A footer of 0 is exactly what `flags.num_cnv_chunks = 0` writes, so it
// reproduces the legacy layout without an on-disk fixture.
TEST(update_aux_test, legacy_zero_num_cnv_chunks_footer)
{
    auto path_template = (MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
                          "monad_update_aux_test_XXXXXX")
                             .native();
    int const fd = ::mkstemp(path_template.data());
    MONAD_ASSERT(fd != -1);
    MONAD_ASSERT(-1 != ::ftruncate(fd, 8UL << 30)); // 8GB
    ::close(fd);
    std::filesystem::path const filename{path_template};

    monad::io::Ring ring1;
    monad::io::Ring ring2;
    monad::io::Buffers testbuf =
        monad::io::make_buffers_for_segregated_read_write(
            ring1,
            ring2,
            2,
            4,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
    monad::async::storage_pool::creation_flags flags;
    flags.chunk_capacity = 24;
    flags.num_cnv_chunks = 0; // legacy footer
    {
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::truncate, flags);
        EXPECT_EQ(pool.chunks(monad::async::storage_pool::cnv), 3);

        monad::async::AsyncIO testio(pool, testbuf);
        monad::mpt::UpdateAux const aux(testio);

        EXPECT_EQ(aux.metadata_ctx().main()->root_offsets.cnv_chunks_len(), 2);
        EXPECT_EQ(
            aux.metadata_ctx().main()->secondary_timeline.cnv_chunks_len(), 0);
    }
    {
        // Reopen exercises map_ring_a_storage — the path that underflowed.
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::open_existing, flags);
        EXPECT_EQ(pool.chunks(monad::async::storage_pool::cnv), 3);
        monad::async::AsyncIO testio(pool, testbuf);
        monad::mpt::UpdateAux const aux(testio);
        EXPECT_EQ(aux.metadata_ctx().main()->root_offsets.cnv_chunks_len(), 2);
        EXPECT_EQ(
            aux.metadata_ctx().main()->secondary_timeline.cnv_chunks_len(), 0);
    }
    remove(filename);
}

// -------------------------------------------------------------------
// Secondary timeline ring and lifecycle tests (UpdateAux-level)
// -------------------------------------------------------------------

TEST(update_aux_test, secondary_ring_empty_after_init)
{
    with_rw_aux([](UpdateAux &aux) {
        // Secondary ring is empty at init — it has no cnv chunks yet and
        // will be allocated chunks on activate_secondary_timeline via an
        // atomic shrink of ring_a.
        auto const ro = aux.metadata_ctx().root_offsets(timeline_id::secondary);
        EXPECT_TRUE(ro.empty());
        EXPECT_EQ(ro.capacity(), 0u);
        EXPECT_EQ(
            aux.metadata_ctx().main()->secondary_timeline.cnv_chunks_len(), 0u);
    });
}

TEST(update_aux_test, secondary_inactive_by_default)
{
    with_rw_aux([](UpdateAux &aux) {
        EXPECT_TRUE(aux.metadata_ctx().timeline_active(timeline_id::primary));
        EXPECT_FALSE(
            aux.metadata_ctx().timeline_active(timeline_id::secondary));
    });
}

// -------------------------------------------------------------------
// State machine kind: per-timeline metadata round-trip
// -------------------------------------------------------------------

TEST(update_aux_test, state_machine_kind_default_ethereum)
{
    // A freshly-initialised pool is zeroed by init_new_pool; ethereum is the
    // zero value, so both rings read back as ethereum until a real kind is
    // stamped (e.g. via monad-mpt --state-machine).
    with_rw_aux([](UpdateAux &aux) {
        EXPECT_EQ(
            aux.metadata_ctx().get_state_machine_kind(timeline_id::primary),
            state_machine_kind::ethereum);
        EXPECT_EQ(
            aux.metadata_ctx().get_state_machine_kind(timeline_id::secondary),
            state_machine_kind::ethereum);
    });
}

TEST(update_aux_test, state_machine_kind_primary_round_trip)
{
    // A non-default value (no registered factory needed for a storage
    // round-trip) proves the byte persists on the primary ring while the
    // secondary keeps its ethereum-zero default.
    auto const other = static_cast<state_machine_kind>(1);
    with_rw_aux([other](UpdateAux &aux) {
        aux.metadata_ctx().set_state_machine_kind(timeline_id::primary, other);
        EXPECT_EQ(
            aux.metadata_ctx().get_state_machine_kind(timeline_id::primary),
            other);
        // Secondary unaffected.
        EXPECT_EQ(
            aux.metadata_ctx().get_state_machine_kind(timeline_id::secondary),
            state_machine_kind::ethereum);
    });
}

TEST(update_aux_test, state_machine_kind_secondary_independent)
{
    // Distinct non-default values prove the two timelines route to
    // independent bytes.
    auto const a = static_cast<state_machine_kind>(1);
    auto const b = static_cast<state_machine_kind>(2);
    with_rw_aux([a, b](UpdateAux &aux) {
        aux.metadata_ctx().set_state_machine_kind(timeline_id::primary, a);
        aux.metadata_ctx().set_state_machine_kind(timeline_id::secondary, b);
        EXPECT_EQ(
            aux.metadata_ctx().get_state_machine_kind(timeline_id::primary), a);
        EXPECT_EQ(
            aux.metadata_ctx().get_state_machine_kind(timeline_id::secondary),
            b);
    });
}

TEST(update_aux_test, state_machine_kind_persists_across_reopen)
{
    // Verifies the kind written through DbMetadataContext lands in stable
    // on-disk bytes (both metadata copies) and is observable after a full
    // close+reopen of the storage pool. Use a non-default value so the
    // assertion can't pass on a freshly-zeroed (ethereum) pool.
    auto const kind = static_cast<state_machine_kind>(1);
    monad::async::storage_pool::creation_flags flags;
    flags.chunk_capacity = 24;
    flags.num_cnv_chunks = 2 + UpdateAux::cnv_chunks_for_db_metadata;

    auto path_template = (MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
                          "state_machine_kind_persists_XXXXXX")
                             .native();
    {
        int const fd = ::mkstemp(path_template.data());
        ASSERT_GE(fd, 0);
        ASSERT_EQ(::ftruncate(fd, 8LL << 30), 0);
        ::close(fd);
    }
    auto const filename = std::filesystem::path(path_template);
    auto const unfilename = monad::make_scope_exit(
        [&]() noexcept { std::filesystem::remove(filename); });

    monad::io::Ring ring1;
    monad::io::Ring ring2;
    auto testbuf = monad::io::make_buffers_for_segregated_read_write(
        ring1,
        ring2,
        2,
        4,
        monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
        monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
    {
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::truncate, flags);
        monad::async::AsyncIO testio(pool, testbuf);
        monad::mpt::UpdateAux aux(testio);
        aux.metadata_ctx().set_state_machine_kind(timeline_id::primary, kind);
    }
    {
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::open_existing, flags);
        monad::async::AsyncIO testio(pool, testbuf);
        monad::mpt::UpdateAux const aux(testio);
        EXPECT_EQ(
            aux.metadata_ctx().get_state_machine_kind(timeline_id::primary),
            kind);
    }
}

// SIZE_ - 1 = 31 cnv chunks is the per-ring cnv_chunks[] cap. num_cnv_chunks
// = SIZE_ + 1 makes ring_total = SIZE_ = 32, one past the array. New-pool
// init must abort rather than write out of bounds into root_offsets_state.
TEST(update_aux_death_test, aborts_when_root_offsets_ring_exceeds_capacity)
{
    std::string templ = (MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
                         "monad_update_aux_ring_cap_test_XXXXXX")
                            .string();
    int const fd = ::mkstemp(templ.data());
    MONAD_ASSERT(fd != -1);
    std::filesystem::path const filename{templ};
    auto const unfilename = monad::make_scope_exit(
        [&]() noexcept { (void)::unlink(filename.c_str()); });
    MONAD_ASSERT(-1 != ::ftruncate(fd, 2UL << 30)); // 2GB

    monad::io::Ring ring1;
    monad::io::Ring ring2;
    monad::io::Buffers testbuf =
        monad::io::make_buffers_for_segregated_read_write(
            ring1,
            ring2,
            2,
            4,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
    monad::async::storage_pool::creation_flags flags;
    flags.chunk_capacity = 24; // 16 MiB chunks keep the temp file small
    flags.num_cnv_chunks =
        static_cast<uint32_t>(detail::db_metadata::root_offsets_ring_t::SIZE_) +
        1; // 33 -> ring_total 32
    monad::async::storage_pool pool(
        filename, monad::async::storage_pool::mode::truncate, flags);
    monad::async::AsyncIO testio(pool, testbuf);

    ASSERT_DEATH(
        { DbMetadataContext const ctx{testio}; }, "exceeds the per-ring");
}

TEST(update_aux_test, activate_deactivate_secondary)
{
    with_rw_aux([](UpdateAux &aux) {
        EXPECT_FALSE(
            aux.metadata_ctx().timeline_active(timeline_id::secondary));

        aux.activate_secondary_timeline();
        EXPECT_TRUE(aux.metadata_ctx().timeline_active(timeline_id::secondary));

        // Header version fields are zeroed on activate so the secondary
        // timeline starts completely empty; fast_forward_next_version on
        // the first secondary write seeds them. With no prior promote,
        // primary_ring_idx==0 so secondary routes to ring_b
        // (secondary_timeline).
        auto const *md = aux.metadata_ctx().main();
        EXPECT_EQ(md->primary_ring_idx, 0u);
        EXPECT_EQ(
            test::DbMetadataTestAccess::version_lower_bound(
                md->secondary_timeline),
            0u);
        EXPECT_EQ(
            test::DbMetadataTestAccess::next_version(md->secondary_timeline),
            0u);
        EXPECT_EQ(md->secondary_timeline_active_, 1u);

        aux.deactivate_secondary_timeline();
        EXPECT_FALSE(
            aux.metadata_ctx().timeline_active(timeline_id::secondary));
        EXPECT_EQ(md->secondary_timeline_active_, 0u);
    });
}

TEST(update_aux_test, activate_initializes_secondary_compaction_to_default)
{
    with_rw_aux([](UpdateAux &aux) {
        // Mutate primary's compaction state away from defaults so the test
        // can prove the secondary does NOT inherit it.
        aux.tl(timeline_id::primary).compact_offsets.fast.set_value(0x1234);
        aux.tl(timeline_id::primary).compact_offsets.slow.set_value(0x5678);

        aux.activate_secondary_timeline();

        // Secondary must start empty regardless of primary's state. Its
        // compaction values are initialised on the first secondary upsert
        // by deserialising prev_root's compact_offsets.
        timeline_compaction_state const default_state{};
        auto const &secondary = aux.tl(timeline_id::secondary);
        EXPECT_EQ(
            secondary.compact_offsets.fast, default_state.compact_offsets.fast);
        EXPECT_EQ(
            secondary.compact_offsets.slow, default_state.compact_offsets.slow);
        EXPECT_EQ(
            secondary.compact_offset_range_fast_,
            default_state.compact_offset_range_fast_);
        EXPECT_EQ(
            secondary.compact_offset_range_slow_,
            default_state.compact_offset_range_slow_);

        aux.deactivate_secondary_timeline();

        // Deactivation also returns to default.
        auto const &reset = aux.tl(timeline_id::secondary);
        EXPECT_EQ(
            reset.compact_offsets.fast, default_state.compact_offsets.fast);
        EXPECT_EQ(
            reset.compact_offsets.slow, default_state.compact_offsets.slow);
    });
}

TEST(update_aux_test, promote_swaps_compaction_state)
{
    with_rw_aux([](UpdateAux &aux) {
        auto pro = aux.metadata_ctx().root_offsets(timeline_id::primary);
        pro.push(chunk_offset_t{1, 0});

        aux.activate_secondary_timeline();
        auto sro = aux.metadata_ctx().root_offsets(timeline_id::secondary);
        sro.push(chunk_offset_t{2, 0});

        // Set distinguishable auto-expire values
        aux.tl(timeline_id::primary).curr_upsert_auto_expire_version = 111;
        aux.tl(timeline_id::secondary).curr_upsert_auto_expire_version = 222;

        aux.promote_secondary_to_primary();

        // Compaction state should be swapped
        EXPECT_EQ(
            aux.tl(timeline_id::primary).curr_upsert_auto_expire_version, 222);
        EXPECT_EQ(
            aux.tl(timeline_id::secondary).curr_upsert_auto_expire_version,
            111);

        aux.deactivate_secondary_timeline();
    });
}

TEST(update_aux_test, lifecycle_updates_both_metadata_copies)
{
    with_rw_aux([](UpdateAux &aux) {
        aux.activate_secondary_timeline();

        // Verify both metadata copies have matching secondary header
        auto ro0 = aux.metadata_ctx().root_offsets(timeline_id::secondary, 0);
        auto ro1 = aux.metadata_ctx().root_offsets(timeline_id::secondary, 1);
        EXPECT_EQ(ro0.max_version(), ro1.max_version());
        EXPECT_FALSE(ro0.empty());
        EXPECT_FALSE(ro1.empty());

        // Push a root and verify both copies. The first push lands at
        // version 0 because next_version_ starts zero post-activate.
        chunk_offset_t const offset{3, 42};
        ro0.push(offset);
        ro1.push(offset);
        EXPECT_EQ(ro0[0].id, offset.id);
        EXPECT_EQ(ro1[0].id, offset.id);

        // Promote and verify both copies swapped
        aux.promote_secondary_to_primary();
        auto const new_pro0 =
            aux.metadata_ctx().root_offsets(timeline_id::primary, 0);
        auto const new_pro1 =
            aux.metadata_ctx().root_offsets(timeline_id::primary, 1);
        EXPECT_EQ(new_pro0.max_version(), new_pro1.max_version());
        EXPECT_EQ(new_pro0[0].id, offset.id);
        EXPECT_EQ(new_pro1[0].id, offset.id);

        aux.deactivate_secondary_timeline();
    });
}

TEST(update_aux_test, activate_at_version_zero)
{
    with_rw_aux([](UpdateAux &aux) {
        aux.activate_secondary_timeline();
        EXPECT_TRUE(aux.metadata_ctx().timeline_active(timeline_id::secondary));

        // Before any push, next_version_ == 0 so max_version() is
        // INVALID_BLOCK_NUM — min_valid correctly reports INVALID
        EXPECT_EQ(
            aux.metadata_ctx().db_history_min_valid_version(
                timeline_id::secondary),
            INVALID_BLOCK_NUM);

        // After pushing at version 0, the ring is populated
        auto sro = aux.metadata_ctx().root_offsets(timeline_id::secondary);
        sro.push(chunk_offset_t{1, 0});
        EXPECT_EQ(sro.max_version(), 0u);
        EXPECT_TRUE(aux.metadata_ctx().version_is_valid_ondisk(
            0, timeline_id::secondary));
        EXPECT_EQ(
            aux.metadata_ctx().db_history_min_valid_version(
                timeline_id::secondary),
            0u);

        aux.deactivate_secondary_timeline();
    });
}

TEST(update_aux_test, reactivate_after_deactivate)
{
    with_rw_aux([](UpdateAux &aux) {
        // First activation. First push lands at version 0.
        aux.activate_secondary_timeline();
        auto sro = aux.metadata_ctx().root_offsets(timeline_id::secondary);
        chunk_offset_t const first_offset{3, 100};
        sro.push(first_offset);
        EXPECT_EQ(sro[0].id, first_offset.id);
        aux.deactivate_secondary_timeline();

        // Reactivate; next_version_ has been re-zeroed.
        aux.activate_secondary_timeline();
        EXPECT_TRUE(aux.metadata_ctx().timeline_active(timeline_id::secondary));

        // Old data is wiped — ring slots are INVALID_OFFSET, version
        // fields are zero (max_version() == INVALID_BLOCK_NUM).
        auto sro2 = aux.metadata_ctx().root_offsets(timeline_id::secondary);
        EXPECT_EQ(sro2.max_version(), INVALID_BLOCK_NUM);
        EXPECT_EQ(sro2[0], monad::async::INVALID_OFFSET)
            << "Stale data from first activation should be cleared";

        // New push works; lands at version 0 again.
        chunk_offset_t const second_offset{4, 200};
        sro2.push(second_offset);
        EXPECT_EQ(sro2[0].id, second_offset.id);

        aux.deactivate_secondary_timeline();
    });
}

TEST(update_aux_test, secondary_ring_initialized_to_invalid_offset_on_activate)
{
    with_rw_aux([](UpdateAux &aux) {
        // After activation, the secondary ring has been allocated chunks
        // (taken from the shrunk primary) and initialised to
        // INVALID_OFFSET by activate_secondary_header.
        aux.activate_secondary_timeline();
        auto const ro = aux.metadata_ctx().root_offsets(timeline_id::secondary);
        ASSERT_FALSE(ro.empty());
        // Sample a few positions including 0 (which would be a valid index
        // once next_version_ advances past 0).
        EXPECT_EQ(ro[1], monad::async::INVALID_OFFSET);
        EXPECT_EQ(ro[100], monad::async::INVALID_OFFSET);
        aux.deactivate_secondary_timeline();
    });
}

TEST(update_aux_test, secondary_ring_push_and_read)
{
    with_rw_aux([](UpdateAux &aux) {
        aux.activate_secondary_timeline();

        // Post-activate the secondary starts empty: next_version_ == 0,
        // so max_version() reports INVALID_BLOCK_NUM.
        auto ro = aux.metadata_ctx().root_offsets(timeline_id::secondary);
        EXPECT_EQ(ro.max_version(), INVALID_BLOCK_NUM);

        // First push lands at version 0.
        chunk_offset_t const test_offset{3, 42};
        ro.push(test_offset);
        EXPECT_EQ(ro.max_version(), 0u);
        EXPECT_EQ(ro[0].id, test_offset.id);
        EXPECT_EQ(ro[0].offset, test_offset.offset);

        // Primary ring unaffected
        auto const pro = aux.metadata_ctx().root_offsets(timeline_id::primary);
        EXPECT_EQ(pro.max_version(), INVALID_BLOCK_NUM);

        aux.deactivate_secondary_timeline();
    });
}

TEST(update_aux_test, promote_secondary_to_primary)
{
    with_rw_aux([](UpdateAux &aux) {
        // Set up primary with a root at version 0
        auto pro = aux.metadata_ctx().root_offsets(timeline_id::primary);
        chunk_offset_t const primary_offset{1, 100};
        pro.push(primary_offset);
        EXPECT_EQ(pro.max_version(), 0u);

        // Activate secondary and push a root. Post-activate the secondary
        // starts empty so the first push lands at version 0.
        aux.activate_secondary_timeline();
        auto sro = aux.metadata_ctx().root_offsets(timeline_id::secondary);
        chunk_offset_t const secondary_offset{2, 200};
        sro.push(secondary_offset);
        EXPECT_EQ(sro.max_version(), 0u);

        // Promote
        aux.promote_secondary_to_primary();

        // After promotion: what was secondary is now primary
        auto const new_pro =
            aux.metadata_ctx().root_offsets(timeline_id::primary);
        EXPECT_EQ(new_pro.max_version(), 0u);
        EXPECT_EQ(new_pro[0].id, secondary_offset.id);

        // What was primary is now secondary
        auto const new_sro =
            aux.metadata_ctx().root_offsets(timeline_id::secondary);
        EXPECT_EQ(new_sro.max_version(), 0u);
        EXPECT_EQ(new_sro[0].id, primary_offset.id);

        // Both timelines are active after promotion
        EXPECT_TRUE(aux.metadata_ctx().timeline_active(timeline_id::primary));
        EXPECT_TRUE(aux.metadata_ctx().timeline_active(timeline_id::secondary));

        aux.deactivate_secondary_timeline();
    });
}

TEST(update_aux_test, db_history_version_queries_per_timeline)
{
    with_rw_aux([](UpdateAux &aux) {
        // Primary starts empty
        EXPECT_EQ(
            aux.metadata_ctx().db_history_max_version(timeline_id::primary),
            INVALID_BLOCK_NUM);

        // Activate secondary. It starts empty (next_version_ == 0), so
        // both min_valid and max_version report INVALID_BLOCK_NUM.
        aux.activate_secondary_timeline();
        EXPECT_EQ(
            aux.metadata_ctx().db_history_min_valid_version(
                timeline_id::secondary),
            INVALID_BLOCK_NUM);
        EXPECT_EQ(
            aux.metadata_ctx().db_history_max_version(timeline_id::secondary),
            INVALID_BLOCK_NUM);

        // First push lands at version 0.
        auto sro = aux.metadata_ctx().root_offsets(timeline_id::secondary);
        sro.push(chunk_offset_t{1, 0});
        EXPECT_EQ(
            aux.metadata_ctx().db_history_max_version(timeline_id::secondary),
            0u);

        // Primary queries are independent
        EXPECT_EQ(
            aux.metadata_ctx().db_history_max_version(timeline_id::primary),
            INVALID_BLOCK_NUM);

        aux.deactivate_secondary_timeline();
    });
}

// Promote must be persistent across restart. The on-disk
// primary_ring_idx byte selects which physical ring is the logical
// primary at reopen time; without it, map_ring_a_storage /
// map_ring_b_storage would always pair ring_a with the primary role
// regardless of whether promote had run, producing a silent
// header/data mismatch against ring_b's header state.
//
// Exercises DbMetadataContext directly — skips UpdateAux::init's
// rewind_to_match_offsets path which requires a consistent node-writer
// state and is orthogonal to this test's scope.
TEST(update_aux_test, promote_persists_across_reopen)
{
    std::filesystem::path const filename{
        MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
        "monad_update_aux_promote_persist_XXXXXX"};
    int const fd = ::mkstemp((char *)filename.native().data());
    MONAD_ASSERT(fd != -1);
    MONAD_ASSERT(-1 != ::ftruncate(fd, 8UL << 30)); // 8GB

    monad::async::storage_pool::creation_flags flags;
    flags.chunk_capacity = 24;
    flags.num_cnv_chunks = 5;

    chunk_offset_t const primary_before{1, 0};
    chunk_offset_t const secondary_before{2, 0};

    // Session 1: init pool, activate + push to both rings, promote.
    {
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::truncate, flags);
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers testbuf =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testbuf);
        DbMetadataContext ctx{testio};
        ASSERT_TRUE(ctx.is_new_pool());
        ctx.init_new_pool(AUX_TEST_HISTORY_LENGTH);

        EXPECT_EQ(ctx.primary_ring_idx(), 0u);

        ctx.root_offsets(timeline_id::primary).push(primary_before);
        ctx.activate_secondary_header();
        ctx.root_offsets(timeline_id::secondary).push(secondary_before);
        ctx.promote_secondary_to_primary_header();

        EXPECT_EQ(ctx.primary_ring_idx(), 1u);
        auto const new_pro = ctx.root_offsets(timeline_id::primary);
        EXPECT_EQ(new_pro[0].id, secondary_before.id);
    }

    // Session 2: reopen. primary_ring_idx must survive.
    {
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::open_existing, flags);
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers testbuf =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testbuf);
        DbMetadataContext const ctx{testio};

        EXPECT_EQ(ctx.primary_ring_idx(), 1u);
        EXPECT_TRUE(ctx.timeline_active(timeline_id::secondary));

        auto const new_pro = ctx.root_offsets(timeline_id::primary);
        EXPECT_EQ(new_pro.max_version(), 0u);
        EXPECT_EQ(new_pro[0].id, secondary_before.id);

        auto const new_sro = ctx.root_offsets(timeline_id::secondary);
        EXPECT_EQ(new_sro.max_version(), 0u);
        EXPECT_EQ(new_sro[0].id, primary_before.id);
    }

    remove(filename);
}

// Crash-recovery test for promote_secondary_to_primary_header. Reproduces
// the state that the pre-intent-log promote could not recover from: the
// flip advances both metadata copies, so a crash after copy 0 flipped but
// before copy 1 did left the two copies durably disagreeing on
// primary_ring_idx with neither dirty — the dirty-bit path needs exactly
// one dirty copy to heal from, so it could not repair this. With the
// intent log, a non-NONE PROMOTE flag drives replay, which re-applies the
// absolute target ring idx to both copies (idempotent) and clears the flag.
TEST(update_aux_test, replay_completes_pending_promote_after_crash)
{
    using monad::mpt::detail::db_metadata;
    std::filesystem::path const filename{
        MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
        "monad_replay_pending_promote_XXXXXX"};
    int const fd = ::mkstemp((char *)filename.native().data());
    MONAD_ASSERT(fd != -1);
    MONAD_ASSERT(-1 != ::ftruncate(fd, 8UL << 30));

    monad::async::storage_pool::creation_flags flags;
    flags.chunk_capacity = 24;
    flags.num_cnv_chunks = 5;

    {
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::truncate, flags);
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers testbuf =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testbuf);
        DbMetadataContext ctx{testio};
        ASSERT_TRUE(ctx.is_new_pool());
        ctx.init_new_pool(AUX_TEST_HISTORY_LENGTH);
        ctx.activate_secondary_header();
        ASSERT_EQ(ctx.primary_ring_idx(), 0u);

        // Stamp the PROMOTE intent (target ring idx 1) on both copies, then
        // apply the flip to copy 0 only — the crash window between the two
        // per-copy stores in the body.
        for (unsigned which = 0; which < 2; which++) {
            auto *const m = const_cast<db_metadata *>(ctx.main(which));
            auto const g = m->hold_dirty();
            m->pending_shrink_grow.op_kind = db_metadata::PENDING_OP_PROMOTE;
            m->pending_shrink_grow.op_param = 1;
        }
        {
            auto *const m0 = const_cast<db_metadata *>(ctx.main(0));
            auto const g = m0->hold_dirty();
            std::atomic_ref<uint8_t>(m0->primary_ring_idx)
                .store(1, std::memory_order_release);
        }
        ASSERT_EQ(ctx.main(0)->primary_ring_idx, 1u);
        ASSERT_EQ(ctx.main(1)->primary_ring_idx, 0u);
        // Dtor unmaps without clearing the flag — simulates the crash.
    }

    {
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::open_existing, flags);
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers testbuf =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testbuf);
        DbMetadataContext const ctx{testio};

        // Replay converged both copies to the target and cleared the flag.
        for (unsigned which = 0; which < 2; which++) {
            auto const *const m = ctx.main(which);
            EXPECT_EQ(
                m->pending_shrink_grow.op_kind, db_metadata::PENDING_OP_NONE);
            EXPECT_EQ(m->primary_ring_idx, 1u);
        }
    }

    remove(filename);
}

// Crash-recovery test for activate_secondary_header. Simulates the
// window where the pending intent flag has been stamped and msync'd
// to disk but the activate body hasn't run yet. (Partial-body replay
// is covered separately by replay_completes_partial_cnv_chunks_move.)
// On reopen, the constructor must replay the activate to completion
// and clear the flag.
TEST(update_aux_test, replay_completes_pending_activate_after_crash)
{
    using monad::mpt::detail::db_metadata;
    std::filesystem::path const filename{
        MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
        "monad_replay_pending_activate_XXXXXX"};
    int const fd = ::mkstemp((char *)filename.native().data());
    MONAD_ASSERT(fd != -1);
    MONAD_ASSERT(-1 != ::ftruncate(fd, 8UL << 30));

    monad::async::storage_pool::creation_flags flags;
    flags.chunk_capacity = 24;
    flags.num_cnv_chunks = 5;

    // Session 1: init pool; stamp pending activate flag manually (as if a
    // crash happened right after set_pending_shrink_grow_ + msync but
    // before do_activate_secondary_body_ started).
    uint32_t target_chunks = 0;
    {
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::truncate, flags);
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers testbuf =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testbuf);
        DbMetadataContext ctx{testio};
        ASSERT_TRUE(ctx.is_new_pool());
        ctx.init_new_pool(AUX_TEST_HISTORY_LENGTH);

        // Primary ring has num_cnv_chunks - 1 = 4 chunks; activate would
        // shrink it to 2. Record the target so session 2 can verify.
        auto const old_chunks = ctx.main()->root_offsets.cnv_chunks_len();
        ASSERT_GE(old_chunks, 2u);
        ASSERT_EQ(old_chunks & (old_chunks - 1), 0u);
        target_chunks = old_chunks / 2;

        // Stamp pending flag on both copies under hold_dirty.
        for (unsigned which = 0; which < 2; which++) {
            auto *const m = const_cast<db_metadata *>(ctx.main(which));
            auto const g = m->hold_dirty();
            m->pending_shrink_grow.op_kind = db_metadata::PENDING_OP_ACTIVATE;
            m->pending_shrink_grow.op_param = target_chunks;
        }
        // Dtor runs: DbMetadataContext unmaps without clearing the flag,
        // simulating a crash before clear_pending_shrink_grow_.
    }

    // Session 2: reopen. Replay must finish the activate.
    {
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::open_existing, flags);
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers testbuf =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testbuf);
        DbMetadataContext const ctx{testio};

        // Flag cleared on both copies.
        for (unsigned which = 0; which < 2; which++) {
            auto const *const m = ctx.main(which);
            EXPECT_EQ(
                m->pending_shrink_grow.op_kind, db_metadata::PENDING_OP_NONE);
        }
        // Activate completed: primary shrunk to target, secondary active.
        EXPECT_TRUE(ctx.timeline_active(timeline_id::secondary));
        EXPECT_EQ(ctx.main()->root_offsets.cnv_chunks_len(), target_chunks);
        EXPECT_EQ(
            ctx.main()->secondary_timeline.cnv_chunks_len(), target_chunks);
        // Secondary version fields stay zero through replay — first
        // upsert seeds them via fast_forward_next_version.
        EXPECT_EQ(
            test::DbMetadataTestAccess::version_lower_bound(
                ctx.main()->secondary_timeline),
            0u);
        EXPECT_EQ(
            test::DbMetadataTestAccess::next_version(
                ctx.main()->secondary_timeline),
            0u);
    }

    remove(filename);
}

// Replay against a state where the activate body has already fully
// committed — the crash happened between the post-body sync and the
// flag-clear msync. Replay re-runs the body (idempotent), notices the
// commit is already done, and clears the flag. In production this
// corresponds to a crash after sync_ring_data_to_disk_ +
// sync_metadata_to_disk_ but before clear_pending_shrink_grow_'s msync
// reached disk; at that moment the writer is still inside
// activate_secondary_header (no pushes have resumed), so the replay's
// secondary-ring memset + version-field rewrite cannot clobber live
// data. The test reconstructs that state synthetically by running
// activate to completion and then re-stamping the flag.
TEST(update_aux_test, replay_is_noop_when_activate_already_committed)
{
    using monad::mpt::detail::db_metadata;
    std::filesystem::path const filename{
        MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
        "monad_replay_already_committed_XXXXXX"};
    int const fd = ::mkstemp((char *)filename.native().data());
    MONAD_ASSERT(fd != -1);
    MONAD_ASSERT(-1 != ::ftruncate(fd, 8UL << 30));

    monad::async::storage_pool::creation_flags flags;
    flags.chunk_capacity = 24;
    flags.num_cnv_chunks = 5;

    uint32_t target_chunks = 0;

    {
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::truncate, flags);
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers testbuf =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testbuf);
        DbMetadataContext ctx{testio};
        ASSERT_TRUE(ctx.is_new_pool());
        ctx.init_new_pool(AUX_TEST_HISTORY_LENGTH);

        target_chunks = ctx.main()->root_offsets.cnv_chunks_len() / 2;

        // Fully activate. No subsequent pushes — in production the
        // modelled crash happens while the writer is still inside
        // activate_secondary_header (post-body-sync, pre-flag-clear-
        // msync), so no push has ever touched the post-activate state.
        ctx.activate_secondary_header();

        // Stamp the pending flag back on — simulates a crash after the
        // body finished but before the flag-clear msync completed.
        for (unsigned which = 0; which < 2; which++) {
            auto *const m = const_cast<db_metadata *>(ctx.main(which));
            auto const g = m->hold_dirty();
            m->pending_shrink_grow.op_kind = db_metadata::PENDING_OP_ACTIVATE;
            m->pending_shrink_grow.op_param = target_chunks;
        }
    }

    {
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::open_existing, flags);
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers testbuf =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testbuf);
        DbMetadataContext const ctx{testio};

        for (unsigned which = 0; which < 2; which++) {
            auto const *const m = ctx.main(which);
            EXPECT_EQ(
                m->pending_shrink_grow.op_kind, db_metadata::PENDING_OP_NONE);
        }
        EXPECT_TRUE(ctx.timeline_active(timeline_id::secondary));
        EXPECT_EQ(ctx.main()->root_offsets.cnv_chunks_len(), target_chunks);
        EXPECT_EQ(
            ctx.main()->secondary_timeline.cnv_chunks_len(), target_chunks);
    }

    remove(filename);
}

// Replay for pending deactivate. DB starts in the post-activate state
// (secondary active, primary shrunk); simulates a crash after the
// deactivate intent flag was stamped but before the deactivate body
// ran. Replay must restore the primary to full size and mark secondary
// inactive.
TEST(update_aux_test, replay_completes_pending_deactivate_after_crash)
{
    using monad::mpt::detail::db_metadata;
    std::filesystem::path const filename{
        MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
        "monad_replay_pending_deactivate_XXXXXX"};
    int const fd = ::mkstemp((char *)filename.native().data());
    MONAD_ASSERT(fd != -1);
    MONAD_ASSERT(-1 != ::ftruncate(fd, 8UL << 30));

    monad::async::storage_pool::creation_flags flags;
    flags.chunk_capacity = 24;
    flags.num_cnv_chunks = 5;

    uint32_t target_chunks = 0;
    {
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::truncate, flags);
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers testbuf =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testbuf);
        DbMetadataContext ctx{testio};
        ASSERT_TRUE(ctx.is_new_pool());
        ctx.init_new_pool(AUX_TEST_HISTORY_LENGTH);

        ctx.activate_secondary_header();
        auto const primary_after_activate =
            ctx.main()->root_offsets.cnv_chunks_len();
        auto const secondary_after_activate =
            ctx.main()->secondary_timeline.cnv_chunks_len();
        target_chunks = primary_after_activate + secondary_after_activate;

        // Stamp pending deactivate flag on both copies.
        for (unsigned which = 0; which < 2; which++) {
            auto *const m = const_cast<db_metadata *>(ctx.main(which));
            auto const g = m->hold_dirty();
            m->pending_shrink_grow.op_kind = db_metadata::PENDING_OP_DEACTIVATE;
            m->pending_shrink_grow.op_param = target_chunks;
        }
    }

    {
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::open_existing, flags);
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers testbuf =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testbuf);
        DbMetadataContext const ctx{testio};

        for (unsigned which = 0; which < 2; which++) {
            auto const *const m = ctx.main(which);
            EXPECT_EQ(
                m->pending_shrink_grow.op_kind, db_metadata::PENDING_OP_NONE);
        }
        EXPECT_FALSE(ctx.timeline_active(timeline_id::secondary));
        EXPECT_EQ(ctx.main()->root_offsets.cnv_chunks_len(), target_chunks);
        EXPECT_EQ(ctx.main()->secondary_timeline.cnv_chunks_len(), 0u);
    }

    remove(filename);
}

// Replay exercises the cnv_chunks[] idempotency guard. We stamp the
// pending flag and then hand-apply a partial chunk move (one of two
// expected moves), simulating a crash in the middle of step 4 of
// do_activate_secondary_body_. Replay on reopen must finish the
// remaining move without clobbering the already-moved entry.
TEST(update_aux_test, replay_completes_partial_cnv_chunks_move)
{
    using monad::mpt::detail::db_metadata;
    std::filesystem::path const filename{
        MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
        "monad_replay_partial_cnv_chunks_XXXXXX"};
    int const fd = ::mkstemp((char *)filename.native().data());
    MONAD_ASSERT(fd != -1);
    MONAD_ASSERT(-1 != ::ftruncate(fd, 8UL << 30));

    monad::async::storage_pool::creation_flags flags;
    flags.chunk_capacity = 24;
    flags.num_cnv_chunks = 5; // 4 ring chunks → activate shrinks to 2

    uint32_t target_chunks = 0;
    uint32_t already_moved_id = db_metadata::NULL_CHUNK;
    uint32_t not_yet_moved_id = db_metadata::NULL_CHUNK;
    {
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::truncate, flags);
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers testbuf =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testbuf);
        DbMetadataContext ctx{testio};
        ASSERT_TRUE(ctx.is_new_pool());
        ctx.init_new_pool(AUX_TEST_HISTORY_LENGTH);

        auto const old_chunks = ctx.main()->root_offsets.cnv_chunks_len();
        ASSERT_EQ(old_chunks, 4u);
        target_chunks = old_chunks / 2;
        ASSERT_EQ(target_chunks, 2u);

        // Snapshot which chunks activate would move (the second half of
        // the primary ring's cnv_chunks list).
        already_moved_id =
            test::DbMetadataTestAccess::storage(ctx.main()->root_offsets)
                .cnv_chunks[target_chunks + 0]
                .cnv_chunk_id;
        not_yet_moved_id =
            test::DbMetadataTestAccess::storage(ctx.main()->root_offsets)
                .cnv_chunks[target_chunks + 1]
                .cnv_chunk_id;
        ASSERT_NE(already_moved_id, db_metadata::NULL_CHUNK);
        ASSERT_NE(not_yet_moved_id, db_metadata::NULL_CHUNK);
        ASSERT_NE(already_moved_id, not_yet_moved_id);

        for (unsigned which = 0; which < 2; which++) {
            auto *const m = const_cast<db_metadata *>(ctx.main(which));
            auto const g = m->hold_dirty();
            m->pending_shrink_grow.op_kind = db_metadata::PENDING_OP_ACTIVATE;
            m->pending_shrink_grow.op_param = target_chunks;

            // Hand-apply the first move only (primary→secondary for k=0).
            // Leave k=1 at pristine pre-move state.
            auto &pstore = test::DbMetadataTestAccess::storage(m->root_offsets);
            auto &sstore =
                test::DbMetadataTestAccess::storage(m->secondary_timeline);
            sstore.cnv_chunks[0].high_bits_all_set = uint32_t(-1);
            sstore.cnv_chunks[0].cnv_chunk_id = already_moved_id;
            pstore.cnv_chunks[target_chunks + 0].cnv_chunk_id =
                db_metadata::NULL_CHUNK;
        }
    }

    {
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::open_existing, flags);
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers testbuf =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testbuf);
        DbMetadataContext const ctx{testio};

        for (unsigned which = 0; which < 2; which++) {
            auto const *const m = ctx.main(which);
            EXPECT_EQ(
                m->pending_shrink_grow.op_kind, db_metadata::PENDING_OP_NONE);
            auto const &pstore =
                test::DbMetadataTestAccess::storage(m->root_offsets);
            auto const &sstore =
                test::DbMetadataTestAccess::storage(m->secondary_timeline);

            // The already-moved entry survived — the idempotency guard's
            // "skip if destination already has a valid id" branch didn't
            // re-move it or wipe it.
            EXPECT_EQ(sstore.cnv_chunks[0].cnv_chunk_id, already_moved_id);
            // The not-yet-moved entry was completed by replay.
            EXPECT_EQ(sstore.cnv_chunks[1].cnv_chunk_id, not_yet_moved_id);
            // Source slots on primary are cleared.
            EXPECT_EQ(
                pstore.cnv_chunks[target_chunks + 0].cnv_chunk_id,
                db_metadata::NULL_CHUNK);
            EXPECT_EQ(
                pstore.cnv_chunks[target_chunks + 1].cnv_chunk_id,
                db_metadata::NULL_CHUNK);
            EXPECT_EQ(pstore.cnv_chunks_len, target_chunks);
            EXPECT_EQ(sstore.cnv_chunks_len, target_chunks);
        }
        EXPECT_TRUE(ctx.timeline_active(timeline_id::secondary));
    }

    remove(filename);
}

// Replay preserves primary ring-data at slots outside the shrink/grow
// rewrite region. We push a real chunk_offset_t to version 0 on
// primary, stamp the pending activate flag without running the body,
// reopen, and confirm the offset at version 0 is still readable after
// replay completes the shrink. Position 0 under both old_cap and
// new_cap maps to the same slot, so this validates that the replay
// body does not corrupt low positions.
TEST(update_aux_test, replay_preserves_primary_low_positions)
{
    using monad::mpt::detail::db_metadata;
    std::filesystem::path const filename{
        MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
        "monad_replay_preserves_primary_XXXXXX"};
    int const fd = ::mkstemp((char *)filename.native().data());
    MONAD_ASSERT(fd != -1);
    MONAD_ASSERT(-1 != ::ftruncate(fd, 8UL << 30));

    monad::async::storage_pool::creation_flags flags;
    flags.chunk_capacity = 24;
    flags.num_cnv_chunks = 5;

    chunk_offset_t const pushed{7, 12345};
    uint32_t target_chunks = 0;
    {
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::truncate, flags);
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers testbuf =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testbuf);
        DbMetadataContext ctx{testio};
        ASSERT_TRUE(ctx.is_new_pool());
        ctx.init_new_pool(AUX_TEST_HISTORY_LENGTH);

        // Push a real offset to primary at version 0.
        ctx.root_offsets(timeline_id::primary).push(pushed);
        EXPECT_EQ(ctx.root_offsets(timeline_id::primary)[0].id, pushed.id);

        target_chunks = ctx.main()->root_offsets.cnv_chunks_len() / 2;
        for (unsigned which = 0; which < 2; which++) {
            auto *const m = const_cast<db_metadata *>(ctx.main(which));
            auto const g = m->hold_dirty();
            m->pending_shrink_grow.op_kind = db_metadata::PENDING_OP_ACTIVATE;
            m->pending_shrink_grow.op_param = target_chunks;
        }
    }

    {
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::open_existing, flags);
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers testbuf =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testbuf);
        DbMetadataContext const ctx{testio};

        // Replay ran, flag cleared, secondary active, primary shrunk.
        EXPECT_EQ(
            ctx.main()->pending_shrink_grow.op_kind,
            db_metadata::PENDING_OP_NONE);
        EXPECT_TRUE(ctx.timeline_active(timeline_id::secondary));
        EXPECT_EQ(ctx.main()->root_offsets.cnv_chunks_len(), target_chunks);

        // The pushed offset at version 0 survived replay.
        EXPECT_EQ(ctx.root_offsets(timeline_id::primary)[0].id, pushed.id);
        EXPECT_EQ(ctx.root_offsets(timeline_id::primary).max_version(), 0u);
    }

    remove(filename);
}

// Replay recovers from a crash that landed between the two per-copy
// stamp scopes in set_pending_shrink_grow_: copy 0 has the flag set,
// copy 1 is still pristine. Both copies are clean (neither dirty), so
// dirty-bit recovery does nothing. Replay must still fire because copy 0
// carries a pending op, and converge both copies to the completed state.
TEST(update_aux_test, replay_handles_single_copy_pending_stamp)
{
    using monad::mpt::detail::db_metadata;
    std::filesystem::path const filename{
        MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
        "monad_replay_single_copy_pending_XXXXXX"};
    int const fd = ::mkstemp((char *)filename.native().data());
    MONAD_ASSERT(fd != -1);
    MONAD_ASSERT(-1 != ::ftruncate(fd, 8UL << 30));

    monad::async::storage_pool::creation_flags flags;
    flags.chunk_capacity = 24;
    flags.num_cnv_chunks = 5;

    uint32_t target_chunks = 0;
    {
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::truncate, flags);
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers testbuf =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testbuf);
        DbMetadataContext ctx{testio};
        ASSERT_TRUE(ctx.is_new_pool());
        ctx.init_new_pool(AUX_TEST_HISTORY_LENGTH);

        target_chunks = ctx.main()->root_offsets.cnv_chunks_len() / 2;

        // Stamp pending on copy 0 ONLY. Leave copy 1 entirely unmodified
        // (op_kind == NONE).
        auto *const m0 = const_cast<db_metadata *>(ctx.main(0));
        auto const g0 = m0->hold_dirty();
        m0->pending_shrink_grow.op_kind = db_metadata::PENDING_OP_ACTIVATE;
        m0->pending_shrink_grow.op_param = target_chunks;
    }

    {
        monad::async::storage_pool pool(
            filename, monad::async::storage_pool::mode::open_existing, flags);
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers testbuf =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testbuf);
        DbMetadataContext const ctx{testio};

        for (unsigned which = 0; which < 2; which++) {
            auto const *const m = ctx.main(which);
            EXPECT_EQ(
                m->pending_shrink_grow.op_kind, db_metadata::PENDING_OP_NONE)
                << "copy " << which << " op_kind should be NONE after replay";
        }
        EXPECT_TRUE(ctx.timeline_active(timeline_id::secondary));
    }

    remove(filename);
}

TEST(update_aux_test, version_is_valid_ondisk_per_timeline)
{
    with_rw_aux([](UpdateAux &aux) {
        // Push to primary at version 0; advance to version 1 to leave a
        // version 0 valid on primary that the secondary lacks.
        auto pro = aux.metadata_ctx().root_offsets(timeline_id::primary);
        pro.push(chunk_offset_t{1, 0});
        pro.push(chunk_offset_t{1, 100}); // version 1
        EXPECT_TRUE(aux.metadata_ctx().version_is_valid_ondisk(
            0, timeline_id::primary));
        EXPECT_TRUE(aux.metadata_ctx().version_is_valid_ondisk(
            1, timeline_id::primary));
        EXPECT_FALSE(aux.metadata_ctx().version_is_valid_ondisk(
            2, timeline_id::primary));

        // Activate secondary; first push lands at version 0.
        aux.activate_secondary_timeline();
        auto sro = aux.metadata_ctx().root_offsets(timeline_id::secondary);
        sro.push(chunk_offset_t{2, 0});

        // Version 0 valid on both timelines now.
        EXPECT_TRUE(aux.metadata_ctx().version_is_valid_ondisk(
            0, timeline_id::secondary));
        EXPECT_TRUE(aux.metadata_ctx().version_is_valid_ondisk(
            0, timeline_id::primary));

        // Version 1 valid on primary, not on secondary.
        EXPECT_TRUE(aux.metadata_ctx().version_is_valid_ondisk(
            1, timeline_id::primary));
        EXPECT_FALSE(aux.metadata_ctx().version_is_valid_ondisk(
            1, timeline_id::secondary));

        aux.deactivate_secondary_timeline();
    });
}

// -------------------------------------------------------------------
// rewind_to_version + clear_ondisk_db dual-timeline behavior
// -------------------------------------------------------------------

namespace
{
    // Burn BYTES bytes on the current fast writer chunk and return the
    // chunk_offset_t (with spare bits set to BYTES/DISK_PAGE_SIZE) that points
    // at where the write started. Caller appends this to a ring and advances
    // db_offsets so rewind_to_match_offsets's invariants hold.
    constexpr size_t FAKE_ROOT_BYTES = 1024;

    chunk_offset_t
    fake_root_write(monad::async::storage_pool &pool, UpdateAux &aux)
    {
        chunk_offset_t const off_before =
            aux.node_writer_fast->sender().offset();
        (void)pool.chunk(monad::async::storage_pool::seq, off_before.id)
            .write_fd(FAKE_ROOT_BYTES);
        chunk_offset_t off_with_spare = off_before; // mutated by set_spare
        off_with_spare.set_spare(FAKE_ROOT_BYTES / DISK_PAGE_SIZE);
        auto const off_after = off_before.add_to_offset(FAKE_ROOT_BYTES);
        aux.metadata_ctx().advance_db_offsets_to(
            off_after, aux.metadata_ctx().get_start_of_wip_slow_offset());
        return off_with_spare;
    }

    void primary_write(
        monad::async::storage_pool &pool, UpdateAux &aux, uint64_t version)
    {
        auto const off = fake_root_write(pool, aux);
        auto &mctx = aux.metadata_ctx();
        auto const max_ver = mctx.db_history_max_version();
        if (max_ver == INVALID_BLOCK_NUM) {
            mctx.fast_forward_next_version(version, timeline_id::primary);
            mctx.append_root_offset(off, timeline_id::primary);
        }
        else if (version <= max_ver) {
            mctx.update_root_offset(version, off, timeline_id::primary);
        }
        else {
            MONAD_ASSERT(version == max_ver + 1);
            mctx.append_root_offset(off, timeline_id::primary);
        }
    }

    void secondary_write(
        monad::async::storage_pool &pool, UpdateAux &aux, uint64_t version)
    {
        auto const off = fake_root_write(pool, aux);
        auto &mctx = aux.metadata_ctx();
        auto const max_ver =
            mctx.db_history_max_version(timeline_id::secondary);
        if (max_ver == INVALID_BLOCK_NUM) {
            mctx.fast_forward_next_version(version, timeline_id::secondary);
            mctx.append_root_offset(off, timeline_id::secondary);
        }
        else if (version <= max_ver) {
            mctx.update_root_offset(version, off, timeline_id::secondary);
        }
        else {
            MONAD_ASSERT(version == max_ver + 1);
            mctx.append_root_offset(off, timeline_id::secondary);
        }
    }
}

// Secondary lags primary (lower max_version); primary rewind must not
// touch secondary's ring or destroy chunks holding secondary's nodes.
TEST(update_aux_test, rewind_preserves_lagging_secondary)
{
    monad::async::storage_pool pool(monad::async::use_anonymous_inode_tag{});
    monad::io::Ring ring1;
    monad::io::Ring ring2;
    monad::io::Buffers testbuf =
        monad::io::make_buffers_for_segregated_read_write(
            ring1,
            ring2,
            2,
            4,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
    monad::async::AsyncIO testio(pool, testbuf);
    UpdateAux aux{testio, AUX_TEST_HISTORY_LENGTH};
    auto &mctx = aux.metadata_ctx();

    // Primary versions 0..4.
    for (uint64_t v = 0; v <= 4; ++v) {
        primary_write(pool, aux, v);
    }
    // Activate secondary; secondary versions 0..1 (lagging).
    aux.activate_secondary_timeline();
    secondary_write(pool, aux, 0);
    secondary_write(pool, aux, 1);
    // More primary versions 5..9.
    for (uint64_t v = 5; v <= 9; ++v) {
        primary_write(pool, aux, v);
    }
    mctx.set_latest_finalized_version(7);

    auto const secondary_v0_before =
        mctx.root_offsets(timeline_id::secondary)[0];
    auto const secondary_v1_before =
        mctx.root_offsets(timeline_id::secondary)[1];

    aux.rewind_to_version(7);

    EXPECT_EQ(mctx.db_history_max_version(timeline_id::primary), 7u);
    EXPECT_TRUE(mctx.timeline_active(timeline_id::secondary));
    EXPECT_EQ(mctx.db_history_max_version(timeline_id::secondary), 1u);
    EXPECT_EQ(
        mctx.root_offsets(timeline_id::secondary)[0], secondary_v0_before);
    EXPECT_EQ(
        mctx.root_offsets(timeline_id::secondary)[1], secondary_v1_before);
    EXPECT_TRUE(mctx.version_is_valid_ondisk(1, timeline_id::secondary));
    EXPECT_FALSE(mctx.version_is_valid_ondisk(2, timeline_id::secondary));
    EXPECT_FALSE(mctx.version_is_valid_ondisk(8, timeline_id::primary));

    aux.deactivate_secondary_timeline();
}

// Secondary caught up past the rewind point; both rings must discard
// speculative entries above the target.
TEST(update_aux_test, rewind_discards_speculative_on_both_timelines)
{
    monad::async::storage_pool pool(monad::async::use_anonymous_inode_tag{});
    monad::io::Ring ring1;
    monad::io::Ring ring2;
    monad::io::Buffers testbuf =
        monad::io::make_buffers_for_segregated_read_write(
            ring1,
            ring2,
            2,
            4,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
    monad::async::AsyncIO testio(pool, testbuf);
    UpdateAux aux{testio, AUX_TEST_HISTORY_LENGTH};
    auto &mctx = aux.metadata_ctx();

    // Primary versions 0..4.
    for (uint64_t v = 0; v <= 4; ++v) {
        primary_write(pool, aux, v);
    }
    aux.activate_secondary_timeline();
    // Both timelines write versions 5..9. Interleaved real-time order.
    for (uint64_t v = 5; v <= 9; ++v) {
        primary_write(pool, aux, v);
        secondary_write(pool, aux, v - 5); // secondary maps blocks 0..4
    }
    // Secondary now has versions 0..4 (corresponds to primary 5..9 blocks
    // in the migration model — exact mapping doesn't matter here, just that
    // secondary's max > rewind target).
    mctx.set_latest_finalized_version(7);

    aux.rewind_to_version(7);

    EXPECT_EQ(mctx.db_history_max_version(timeline_id::primary), 7u);
    // Secondary's max was 4, and 4 < 7, so secondary is unchanged.
    EXPECT_EQ(mctx.db_history_max_version(timeline_id::secondary), 4u);

    // Now write 3 more secondary versions to push it past the rewind target,
    // then rewind primary again to 2 (lower than secondary's max).
    secondary_write(pool, aux, 5);
    secondary_write(pool, aux, 6);
    secondary_write(pool, aux, 7);
    EXPECT_EQ(mctx.db_history_max_version(timeline_id::secondary), 7u);

    aux.rewind_to_version(2);
    EXPECT_EQ(mctx.db_history_max_version(timeline_id::primary), 2u);
    EXPECT_EQ(mctx.db_history_max_version(timeline_id::secondary), 2u);
    EXPECT_FALSE(mctx.version_is_valid_ondisk(3, timeline_id::primary));
    EXPECT_FALSE(mctx.version_is_valid_ondisk(3, timeline_id::secondary));

    aux.deactivate_secondary_timeline();
}

// Both timelines must persist across an UpdateAux re-init (simulates a
// node restart that triggers rewind_to_latest_finalized internally).
TEST(update_aux_test, rewind_state_survives_reopen)
{
    monad::async::storage_pool pool(monad::async::use_anonymous_inode_tag{});
    monad::io::Ring ring1;
    monad::io::Ring ring2;
    monad::io::Buffers testbuf =
        monad::io::make_buffers_for_segregated_read_write(
            ring1,
            ring2,
            2,
            4,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
    monad::async::AsyncIO testio(pool, testbuf);

    chunk_offset_t secondary_root_at_v1 = INVALID_OFFSET;
    {
        UpdateAux aux{testio, AUX_TEST_HISTORY_LENGTH};
        auto &mctx = aux.metadata_ctx();
        for (uint64_t v = 0; v <= 4; ++v) {
            primary_write(pool, aux, v);
        }
        aux.activate_secondary_timeline();
        secondary_write(pool, aux, 0);
        secondary_write(pool, aux, 1);
        for (uint64_t v = 5; v <= 9; ++v) {
            primary_write(pool, aux, v);
        }
        mctx.set_latest_finalized_version(7);
        secondary_root_at_v1 = mctx.root_offsets(timeline_id::secondary)[1];
        aux.rewind_to_version(7);
    }

    // Reopen the pool with a fresh UpdateAux.
    UpdateAux aux2{testio, AUX_TEST_HISTORY_LENGTH};
    auto const &mctx2 = aux2.metadata_ctx();
    EXPECT_EQ(mctx2.db_history_max_version(timeline_id::primary), 7u);
    EXPECT_TRUE(mctx2.timeline_active(timeline_id::secondary));
    EXPECT_EQ(mctx2.db_history_max_version(timeline_id::secondary), 1u);
    EXPECT_EQ(
        mctx2.root_offsets(timeline_id::secondary)[1], secondary_root_at_v1);
    aux2.deactivate_secondary_timeline();
}

// clear_ondisk_db must keep the secondary active while resetting BOTH
// timelines' rings, not just primary. A populated secondary that survives into
// rewind_to_match_offsets() would leave a root offset ahead of the rewound
// fast/slow offsets and abort.
TEST(update_aux_test, clear_ondisk_db_clears_populated_secondary)
{
    monad::async::storage_pool pool(monad::async::use_anonymous_inode_tag{});
    monad::io::Ring ring1;
    monad::io::Ring ring2;
    monad::io::Buffers testbuf =
        monad::io::make_buffers_for_segregated_read_write(
            ring1,
            ring2,
            2,
            4,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
    monad::async::AsyncIO testio(pool, testbuf);

    UpdateAux aux{testio, AUX_TEST_HISTORY_LENGTH};
    auto const &mctx = aux.metadata_ctx();

    for (uint64_t v = 0; v <= 4; ++v) {
        primary_write(pool, aux, v);
    }
    aux.activate_secondary_timeline();
    EXPECT_TRUE(mctx.timeline_active(timeline_id::secondary));
    secondary_write(pool, aux, 0);
    secondary_write(pool, aux, 1);
    secondary_write(pool, aux, 2);
    EXPECT_EQ(mctx.db_history_max_version(timeline_id::primary), 4u);
    EXPECT_EQ(mctx.db_history_max_version(timeline_id::secondary), 2u);

    aux.clear_ondisk_db();

    EXPECT_TRUE(mctx.timeline_active(timeline_id::secondary));
    EXPECT_EQ(
        mctx.db_history_max_version(timeline_id::primary), INVALID_BLOCK_NUM);
    EXPECT_EQ(
        mctx.db_history_max_version(timeline_id::secondary), INVALID_BLOCK_NUM);

    aux.deactivate_secondary_timeline();
}

namespace
{
    using detail::db_metadata;
    using test::edit_metadata_copies;
    using test::provision_monad008_metadata;
    using test::provision_monad008_pool;

    // The first count MONAD008's 20-bit field cannot hold.
    constexpr uint64_t NARROW_LIMIT = uint64_t{1} << 20;

    monad::async::storage_pool make_upgrade_pool(bool const allow_migration)
    {
        monad::async::storage_pool::creation_flags flags;
        flags.chunk_capacity = 24;
        flags.allow_migration = allow_migration;
        return monad::async::storage_pool{
            monad::async::use_anonymous_sized_inode_tag{},
            (off_t{1} << 30) + 24576,
            flags};
    }

    // Opens `pool` writable through UpdateAux, as a node does.
    template <class Fn>
    void with_aux(monad::async::storage_pool &pool, Fn &&fn)
    {
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers buffers =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO io(pool, buffers);
        UpdateAux aux{io};
        fn(aux);
    }

    uint32_t move_free_tail_to(
        DbMetadataContext &ctx, DbMetadataContext::chunk_list const list)
    {
        uint32_t const idx = ctx.main()->free_list.end;
        ctx.remove(idx);
        ctx.append(list, idx);
        return idx;
    }

    // Several chunks in each list, with counts reaching just below MONAD008's
    // 20-bit limit, and three primary versions. The write offsets sit at the
    // list tails, so that a writable reopen keeps every list as it is.
    void populate(UpdateAux &aux)
    {
        using chunk_list = DbMetadataContext::chunk_list;
        auto &ctx = aux.metadata_ctx();
        ctx.restart_insertion_counts(chunk_list::fast, NARROW_LIMIT - 3);
        ctx.restart_insertion_counts(chunk_list::slow, NARROW_LIMIT - 2);
        move_free_tail_to(ctx, chunk_list::fast);
        uint32_t const fast_tail = move_free_tail_to(ctx, chunk_list::fast);
        uint32_t const slow_tail = move_free_tail_to(ctx, chunk_list::slow);
        ctx.advance_db_offsets_to(
            chunk_offset_t{fast_tail, 0}, chunk_offset_t{slow_tail, 0});
        for (int v = 0; v < 3; ++v) {
            ctx.append_root_offset(
                chunk_offset_t{ctx.main()->fast_list.begin, 0},
                timeline_id::primary);
        }
    }

    struct identity
    {
        uint64_t count;
        bool in_fast_list;
        bool in_slow_list;

        bool operator==(identity const &) const = default;
    };

    std::ostream &operator<<(std::ostream &os, identity const &i)
    {
        return os << "{" << i.count << ", fast=" << i.in_fast_list
                  << ", slow=" << i.in_slow_list << "}";
    }

    std::vector<uint32_t>
    list_ids(db_metadata const *const m, db_metadata::chunk_info_t const *i)
    {
        std::vector<uint32_t> ret;
        for (; i != nullptr; i = i->next(m)) {
            ret.push_back(i->index(m));
        }
        return ret;
    }

    // What the upgrade must carry over from one metadata copy.
    struct carried_state
    {
        std::vector<identity> identities;
        std::vector<uint32_t> fast;
        std::vector<uint32_t> slow;
        std::vector<uint32_t> free;
        std::vector<uint64_t> record_words; // chunk_records[], two per record
    };

    carried_state carried_state_of(db_metadata const *const m)
    {
        carried_state s;
        for (uint32_t i = 0; i < m->chunk_info_count; ++i) {
            auto const id =
                m->atomic_load_chunk_identity(i, std::memory_order_acquire);
            s.identities.push_back(
                {id.count, bool(id.in_fast_list), bool(id.in_slow_list)});
        }
        s.fast = list_ids(m, m->fast_list_begin());
        s.slow = list_ids(m, m->slow_list_begin());
        s.free = list_ids(m, m->free_list_begin());
        s.record_words.resize(
            size_t(m->chunk_info_count) * sizeof(db_metadata::chunk_record_t) /
            sizeof(uint64_t));
        std::memcpy(
            s.record_words.data(),
            m->chunk_records,
            s.record_words.size() * sizeof(uint64_t));
        return s;
    }

    std::array<carried_state, 2> carried_states_of(UpdateAux const &aux)
    {
        return {
            carried_state_of(aux.metadata_ctx().main(0)),
            carried_state_of(aux.metadata_ctx().main(1))};
    }

    void expect_upgraded(
        UpdateAux const &aux, std::array<carried_state, 2> const &before)
    {
        for (unsigned which = 0; which < 2; ++which) {
            auto const *const m = aux.metadata_ctx().main(which);
            EXPECT_EQ(
                0,
                std::memcmp(
                    m->magic,
                    db_metadata::MAGIC,
                    db_metadata::MAGIC_STRING_LEN))
                << "copy " << which;
            auto const after = carried_state_of(m);
            EXPECT_EQ(after.identities, before[which].identities)
                << "copy " << which;
            EXPECT_EQ(after.fast, before[which].fast) << "copy " << which;
            EXPECT_EQ(after.slow, before[which].slow) << "copy " << which;
            EXPECT_EQ(after.free, before[which].free) << "copy " << which;
            EXPECT_EQ(after.record_words, before[which].record_words)
                << "copy " << which;
        }
    }

    // What a crash leaves partway through migrate_monad008_to_monad009: the
    // records from index `k` up converted, the bytes below them still in the
    // MONAD008 layout, the old magic, and the dirty bit set.
    void interrupt_migration_at(db_metadata *const m, size_t const k)
    {
        size_t const bytes =
            sizeof(db_metadata) +
            size_t(m->chunk_info_count) * sizeof(db_metadata::chunk_record_t);
        std::vector<uint64_t> scratch(bytes / sizeof(uint64_t));
        std::memcpy(scratch.data(), m, bytes);
        detail::migrate_monad008_to_monad009(
            monad::start_lifetime_as<db_metadata>(scratch.data()));
        size_t const from =
            sizeof(db_metadata) + k * sizeof(db_metadata::chunk_record_t);
        std::memcpy(
            reinterpret_cast<std::byte *>(m) + from,
            reinterpret_cast<std::byte const *>(scratch.data()) + from,
            bytes - from);
        m->is_dirty().store(1, std::memory_order_release);
    }

    struct ring_state
    {
        uint64_t min_valid_version;
        uint64_t max_version;
        std::vector<chunk_offset_t> roots;
    };

    ring_state ring_state_of(UpdateAux const &aux, timeline_id const tid)
    {
        auto const &ctx = aux.metadata_ctx();
        ring_state s{
            ctx.db_history_min_valid_version(tid),
            ctx.db_history_max_version(tid),
            {}};
        auto const ro = ctx.root_offsets(tid);
        for (uint64_t v = s.min_valid_version; v <= s.max_version; ++v) {
            s.roots.push_back(ro[v]);
        }
        return s;
    }

    void expect_same_ring(ring_state const &after, ring_state const &before)
    {
        EXPECT_EQ(after.min_valid_version, before.min_valid_version);
        EXPECT_EQ(after.max_version, before.max_version);
        EXPECT_EQ(after.roots, before.roots);
    }
}

TEST(MetadataUpgrade, carries_every_count_and_list_bit)
{
    auto pool = make_upgrade_pool(true);
    std::array<carried_state, 2> before;
    uint64_t min_version = 0;
    uint64_t max_version = 0;
    with_aux(pool, [&](UpdateAux &aux) {
        populate(aux);
        before = carried_states_of(aux);
        min_version = aux.metadata_ctx().db_history_min_valid_version();
        max_version = aux.metadata_ctx().db_history_max_version();
    });
    std::vector<uint64_t> fast_counts;
    for (uint32_t const idx : before[0].fast) {
        fast_counts.push_back(before[0].identities[idx].count);
    }
    ASSERT_EQ(
        fast_counts,
        (std::vector<uint64_t>{
            NARROW_LIMIT - 3, NARROW_LIMIT - 2, NARROW_LIMIT - 1}));
    ASSERT_EQ(max_version, 2u);

    provision_monad008_pool(pool);
    with_aux(pool, [&](UpdateAux &aux) {
        expect_upgraded(aux, before);
        EXPECT_EQ(
            aux.metadata_ctx().db_history_min_valid_version(), min_version);
        EXPECT_EQ(aux.metadata_ctx().db_history_max_version(), max_version);
    });
}

TEST(MetadataUpgrade, carries_a_secondary_timeline_over)
{
    auto pool = make_upgrade_pool(true);
    std::array<carried_state, 2> before;
    ring_state primary_before{};
    ring_state secondary_before{};
    with_aux(pool, [&](UpdateAux &aux) {
        populate(aux);
        aux.activate_secondary_timeline();
        auto &ctx = aux.metadata_ctx();
        for (int v = 0; v < 2; ++v) {
            ctx.append_root_offset(
                chunk_offset_t{ctx.main()->slow_list.begin, 0},
                timeline_id::secondary);
        }
        before = carried_states_of(aux);
        primary_before = ring_state_of(aux, timeline_id::primary);
        secondary_before = ring_state_of(aux, timeline_id::secondary);
    });
    ASSERT_EQ(primary_before.roots.size(), 3u);
    ASSERT_EQ(secondary_before.roots.size(), 2u);

    provision_monad008_pool(pool);
    with_aux(pool, [&](UpdateAux &aux) {
        expect_upgraded(aux, before);
        EXPECT_TRUE(aux.metadata_ctx().timeline_active(timeline_id::secondary));
        expect_same_ring(
            ring_state_of(aux, timeline_id::primary), primary_before);
        expect_same_ring(
            ring_state_of(aux, timeline_id::secondary), secondary_before);
    });
}

TEST(MetadataUpgrade, heals_a_dirty_copy_first)
{
    auto pool = make_upgrade_pool(true);
    std::array<carried_state, 2> before;
    with_aux(pool, [&](UpdateAux &aux) {
        populate(aux);
        before = carried_states_of(aux);
    });

    uint64_t clean_history_length = 0;
    edit_metadata_copies(pool, [&](db_metadata *const m, unsigned const which) {
        provision_monad008_metadata(m);
        if (which == 0) {
            m->is_dirty().store(1, std::memory_order_release);
            m->history_length = ~m->history_length;
        }
        else {
            clean_history_length = m->history_length;
        }
    });
    with_aux(pool, [&](UpdateAux &aux) {
        expect_upgraded(aux, before);
        for (unsigned which = 0; which < 2; ++which) {
            auto const *const m = aux.metadata_ctx().main(which);
            EXPECT_EQ(m->history_length, clean_history_length)
                << "copy " << which;
            EXPECT_FALSE(const_cast<db_metadata *>(m)->is_dirty().load(
                std::memory_order_acquire))
                << "copy " << which;
        }
    });
}

// The damaged copy's clean dirty bit, pending grow and chunk count are all
// garbage, and each would abort the upgrade if it were believed.
TEST(MetadataUpgrade, heals_a_copy_with_neither_magic_from_a_monad008_copy)
{
    for (unsigned damaged = 0; damaged < 2; ++damaged) {
        auto pool = make_upgrade_pool(true);
        std::array<carried_state, 2> before;
        with_aux(pool, [&](UpdateAux &aux) {
            populate(aux);
            before = carried_states_of(aux);
        });
        edit_metadata_copies(
            pool, [&](db_metadata *const m, unsigned const which) {
                provision_monad008_metadata(m);
                if (which == damaged) {
                    std::memset(m->magic, 0xa5, db_metadata::MAGIC_STRING_LEN);
                    m->pending_shrink_grow = {
                        db_metadata::PENDING_OP_GROW, ~uint32_t{0}};
                    m->chunk_info_count = (uint64_t{1} << 20) - 1;
                }
            });
        with_aux(pool, [&](UpdateAux &aux) { expect_upgraded(aux, before); });
    }
}

namespace
{
    // What one copy looked like when the upgrade synced it.
    struct upgrade_sync
    {
        unsigned which;
        bool dirty;
        std::string magic;
        bool sibling_dirty;

        bool operator==(upgrade_sync const &) const = default;
    };

    std::vector<upgrade_sync> upgrade_syncs;

    void record_upgrade_sync(DbMetadataContext const &ctx, unsigned const which)
    {
        auto *const m = const_cast<db_metadata *>(ctx.main(which));
        auto *const sibling = const_cast<db_metadata *>(ctx.main(1 - which));
        upgrade_syncs.push_back(
            {.which = which,
             .dirty = m->is_dirty().load(std::memory_order_acquire) != 0,
             .magic = std::string(m->magic, db_metadata::MAGIC_STRING_LEN),
             .sibling_dirty =
                 sibling->is_dirty().load(std::memory_order_acquire) != 0});
    }
}

// Each copy reaches disk marked dirty before it changes and clean only after
// its new contents, while its sibling stays clean.
TEST(MetadataUpgrade, syncs_each_copy_dirty_rewritten_then_clean_in_turn)
{
    auto pool = make_upgrade_pool(true);
    with_aux(pool, [](UpdateAux &aux) { populate(aux); });
    provision_monad008_pool(pool);

    upgrade_syncs.clear();
    DbMetadataContext::on_upgrade_sync_unit_testing_only = record_upgrade_sync;
    auto const unhook = monad::make_scope_exit([]() noexcept {
        DbMetadataContext::on_upgrade_sync_unit_testing_only = nullptr;
    });
    with_aux(pool, [](UpdateAux &) {});

    std::string const previous{
        db_metadata::PREVIOUS_MAGIC, db_metadata::MAGIC_STRING_LEN};
    std::string const current{
        db_metadata::MAGIC, db_metadata::MAGIC_STRING_LEN};
    std::vector<upgrade_sync> expected;
    for (unsigned which = 0; which < 2; ++which) {
        expected.push_back({which, true, previous, false});
        expected.push_back({which, true, current, false});
        expected.push_back({which, false, current, false});
    }
    EXPECT_EQ(upgrade_syncs, expected);
}

TEST(MetadataUpgrade, resumes_after_a_crash_between_copies)
{
    auto pool = make_upgrade_pool(true);
    std::array<carried_state, 2> before;
    with_aux(pool, [&](UpdateAux &aux) {
        populate(aux);
        before = carried_states_of(aux);
    });

    edit_metadata_copies(pool, [](db_metadata *const m, unsigned const which) {
        provision_monad008_metadata(m);
        if (which == 0) {
            auto const g = m->hold_dirty();
            detail::migrate_monad008_to_monad009(m);
        }
    });
    with_aux(pool, [&](UpdateAux &aux) {
        expect_upgraded(aux, before);
        auto const *const m0 = aux.metadata_ctx().main(0);
        auto const *const m1 = aux.metadata_ctx().main(1);
        size_t const bytes =
            sizeof(db_metadata) +
            size_t(m0->chunk_info_count) * sizeof(db_metadata::chunk_record_t);
        EXPECT_EQ(0, std::memcmp(m0, m1, bytes));
    });
}

// Copy 0 upgraded, copy 1 interrupted partway through its re-layout: copy 1
// is healed from copy 0 across the two layouts.
TEST(MetadataUpgrade, heals_an_interrupted_second_copy_from_the_first)
{
    auto pool = make_upgrade_pool(true);
    std::array<carried_state, 2> before;
    with_aux(pool, [&](UpdateAux &aux) {
        populate(aux);
        before = carried_states_of(aux);
    });

    edit_metadata_copies(pool, [](db_metadata *const m, unsigned const which) {
        provision_monad008_metadata(m);
        if (which == 0) {
            auto const g = m->hold_dirty();
            detail::migrate_monad008_to_monad009(m);
        }
        else {
            interrupt_migration_at(m, m->chunk_info_count / 2);
        }
    });
    with_aux(pool, [&](UpdateAux &aux) { expect_upgraded(aux, before); });
}

// Copy 0 carries MONAD009 but is dirty, as a crash after its magic landed
// leaves it, and copy 1 is still MONAD008: copy 0 is reverted from copy 1
// across the two layouts, then both are upgraded.
TEST(MetadataUpgrade, reverts_a_dirty_first_copy_then_upgrades_both)
{
    auto pool = make_upgrade_pool(true);
    std::array<carried_state, 2> before;
    with_aux(pool, [&](UpdateAux &aux) {
        populate(aux);
        before = carried_states_of(aux);
    });

    edit_metadata_copies(pool, [](db_metadata *const m, unsigned const which) {
        provision_monad008_metadata(m);
        if (which == 0) {
            detail::migrate_monad008_to_monad009(m);
            m->is_dirty().store(1, std::memory_order_release);
            // A dirty copy can hold anything, so its records must come from
            // copy 1.
            reinterpret_cast<std::byte *>(&m->chunk_records[1].identity)[0] ^=
                std::byte{0x5a};
        }
    });
    with_aux(pool, [&](UpdateAux &aux) { expect_upgraded(aux, before); });
}

TEST(MetadataUpgrade, refuses_without_allow_migration)
{
    testing::FLAGS_gtest_death_test_style = "threadsafe";

    auto pool = make_upgrade_pool(false);
    with_aux(pool, [](UpdateAux &) {});
    provision_monad008_pool(pool);
    ASSERT_DEATH(
        with_aux(pool, [](UpdateAux &) {}),
        "Run 'monad-mpt --upgrade --storage <path>'");
}

TEST(MetadataUpgrade, refuses_a_read_only_open_of_monad008)
{
    testing::FLAGS_gtest_death_test_style = "threadsafe";

    auto pool = make_upgrade_pool(false);
    with_aux(pool, [](UpdateAux &) {});
    provision_monad008_pool(pool);
    auto ro_pool = pool.clone_as_read_only();
    monad::io::Ring ring;
    monad::io::Buffers buffers = monad::io::make_buffers_for_read_only(
        ring, 2, monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE);
    monad::async::AsyncIO io(ro_pool, buffers);
    ASSERT_DEATH({ UpdateAux const aux{io}; }, "Run 'monad-mpt --upgrade");
}

// A read-only mapping cannot persist the upgrade, so it is refused even where
// the pool allows migration. clone_as_read_only() never allows migration, so
// the read-only pool is opened from a file with the flag set.
TEST(MetadataUpgrade, refuses_a_read_only_mapping_even_when_allowed)
{
    testing::FLAGS_gtest_death_test_style = "threadsafe";

    using monad::async::storage_pool;
    auto const dev = grow_test::create_temp_file(20 * grow_test::BLKSIZE);
    auto const undev = monad::make_scope_exit(
        [&]() noexcept { std::filesystem::remove(dev); });
    {
        grow_test::opened_db const db{
            dev, storage_pool::mode::create_if_needed};
    }
    {
        storage_pool pool{
            dev,
            storage_pool::mode::open_existing,
            grow_test::small_chunk_flags()};
        provision_monad008_pool(pool);
    }

    auto flags = grow_test::small_chunk_flags();
    flags.open_read_only = true;
    flags.allow_migration = true;
    storage_pool pool{dev, storage_pool::mode::open_existing, flags};
    // The death-test child re-runs this body and dies without running scope
    // guards; unlinking the file while the pool holds it open leaves the
    // child nothing to clean up.
    std::filesystem::remove(dev);
    monad::io::Ring ring;
    monad::io::Buffers buffers = monad::io::make_buffers_for_read_only(
        ring, 2, monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE);
    monad::async::AsyncIO io(pool, buffers);
    ASSERT_DEATH(
        { UpdateAux const aux{io}; },
        "Detected a MONAD008 DB, which requires a writable mapping to upgrade "
        "to MONAD009");
}

TEST(MetadataUpgrade, refuses_while_a_grow_is_pending)
{
    testing::FLAGS_gtest_death_test_style = "threadsafe";

    auto pool = make_upgrade_pool(true);
    with_aux(pool, [](UpdateAux &) {});
    edit_metadata_copies(pool, [](db_metadata *const m, unsigned) {
        provision_monad008_metadata(m);
        m->pending_shrink_grow = {
            db_metadata::PENDING_OP_GROW,
            static_cast<uint32_t>(m->chunk_info_count)};
    });
    ASSERT_DEATH(
        with_aux(pool, [](UpdateAux &) {}), "A device grow is pending");
}

// 8 MiB chunks, the smallest AsyncIO accepts, leave each metadata copy 4 MiB:
// room for 523728 8-byte entries but only 261864 16-byte records. A MONAD009
// pool that size cannot be made, so its MONAD008 header is written by hand.
TEST(MetadataUpgrade, refuses_when_records_outgrow_the_metadata_copy)
{
    testing::FLAGS_gtest_death_test_style = "threadsafe";

    constexpr uint32_t seq_chunks = 300000;
    monad::async::storage_pool::creation_flags flags;
    flags.chunk_capacity = 23;
    flags.allow_migration = true;
    // Each chunk also costs 4 bytes of pool metadata at the device's end.
    off_t const chunks = off_t{flags.num_cnv_chunks} + seq_chunks;
    monad::async::storage_pool pool{
        monad::async::use_anonymous_sized_inode_tag{},
        chunks * ((off_t{1} << 23) + 4) + 8192,
        flags};
    ASSERT_EQ(pool.chunks(monad::async::storage_pool::seq), seq_chunks);
    edit_metadata_copies(pool, [](db_metadata *const m, unsigned) {
        std::memcpy(
            m->magic,
            db_metadata::PREVIOUS_MAGIC,
            db_metadata::MAGIC_STRING_LEN);
        m->chunk_info_count = seq_chunks & 0xfffffU;
    });
    ASSERT_DEATH(
        with_aux(pool, [](UpdateAux &) {}),
        "16-byte chunk records need 4804480 bytes of metadata but only "
        "4194304 are available");
}

// The records fit, but the pool has more chunks than they describe, as an
// old-binary grow interrupted before it stamped PENDING_OP_GROW leaves it. The
// upgrade's own refusal has to fire, before either copy is migrated, rather
// than the generic fit check after it.
TEST(MetadataUpgrade, refuses_when_the_pool_outgrows_the_metadata_copy)
{
    testing::FLAGS_gtest_death_test_style = "threadsafe";

    constexpr uint32_t seq_chunks = 300000;
    constexpr uint32_t described_chunks = 200000;
    monad::async::storage_pool::creation_flags flags;
    flags.chunk_capacity = 23;
    flags.allow_migration = true;
    off_t const chunks = off_t{flags.num_cnv_chunks} + seq_chunks;
    monad::async::storage_pool pool{
        monad::async::use_anonymous_sized_inode_tag{},
        chunks * ((off_t{1} << 23) + 4) + 8192,
        flags};
    ASSERT_EQ(pool.chunks(monad::async::storage_pool::seq), seq_chunks);
    edit_metadata_copies(pool, [](db_metadata *const m, unsigned) {
        std::memcpy(
            m->magic,
            db_metadata::PREVIOUS_MAGIC,
            db_metadata::MAGIC_STRING_LEN);
        m->chunk_info_count = described_chunks & 0xfffffU;
    });
    ASSERT_DEATH(
        with_aux(pool, [](UpdateAux &) {}),
        "16-byte chunk records need 4804480 bytes of metadata but only "
        "4194304 are available");
}

TEST(MetadataUpgrade, is_a_no_op_on_monad009)
{
    auto pool = make_upgrade_pool(true);
    std::array<carried_state, 2> before;
    with_aux(pool, [&](UpdateAux &aux) {
        populate(aux);
        before = carried_states_of(aux);
    });
    with_aux(pool, [&](UpdateAux &aux) { expect_upgraded(aux, before); });
}

TEST(MetadataUpgrade, grow_extends_records_after_upgrade)
{
    using monad::async::storage_pool;
    auto const dev = grow_test::create_temp_file(20 * grow_test::BLKSIZE);
    auto const undev = monad::make_scope_exit(
        [&]() noexcept { std::filesystem::remove(dev); });
    {
        grow_test::opened_db db{dev, storage_pool::mode::create_if_needed};
        populate(db.aux);
    }
    {
        storage_pool pool{
            dev,
            storage_pool::mode::open_existing,
            grow_test::small_chunk_flags()};
        provision_monad008_pool(pool);
    }

    monad::async::file_offset_t recorded = 0;
    uint32_t chunks_before = 0;
    std::vector<uint32_t> free_before;
    {
        auto flags = grow_test::small_chunk_flags();
        flags.allow_migration = true;
        grow_test::opened_db const db{
            dev, storage_pool::mode::open_existing, flags};
        auto const *const m = db.aux.metadata_ctx().main();
        ASSERT_EQ(
            0,
            std::memcmp(
                m->magic, db_metadata::MAGIC, db_metadata::MAGIC_STRING_LEN));
        recorded = m->recorded_device_size;
        chunks_before = static_cast<uint32_t>(m->chunk_info_count);
        free_before = grow_test::free_list_ids(m);
    }
    grow_test::extend_in_place(dev, 30 * grow_test::BLKSIZE + 16384);

    grow_test::opened_db db{
        dev, storage_pool::mode::grow, grow_test::grow_flags(recorded)};
    auto &ctx = db.aux.metadata_ctx();
    auto const chunks_after =
        static_cast<uint32_t>(ctx.main()->chunk_info_count);
    ASSERT_GT(chunks_after, chunks_before);
    for (unsigned which = 0; which < 2; ++which) {
        auto const *const m = ctx.main(which);
        auto const free_after = grow_test::free_list_ids(m);
        ASSERT_EQ(
            free_after.size(),
            free_before.size() + (chunks_after - chunks_before));
        EXPECT_TRUE(std::equal(
            free_before.begin(), free_before.end(), free_after.begin()))
            << "copy " << which;
        for (uint32_t n = chunks_before; n < chunks_after; ++n) {
            EXPECT_EQ(free_after[free_before.size() + (n - chunks_before)], n)
                << "copy " << which;
        }
        for (size_t n = 1; n < free_after.size(); ++n) {
            EXPECT_EQ(
                m->insertion_count(free_after[n]),
                m->insertion_count(free_after[n - 1]) + 1)
                << "copy " << which << " free slot " << n;
        }
    }

    uint32_t const appended =
        move_free_tail_to(ctx, DbMetadataContext::chunk_list::fast);
    EXPECT_GE(appended, chunks_before);
    for (unsigned which = 0; which < 2; ++which) {
        auto const id = ctx.main(which)->atomic_load_chunk_identity(
            appended, std::memory_order_acquire);
        EXPECT_EQ(uint64_t(id.count), NARROW_LIMIT) << "copy " << which;
        EXPECT_TRUE(id.in_fast_list) << "copy " << which;
        EXPECT_FALSE(id.in_slow_list) << "copy " << which;
    }
}
