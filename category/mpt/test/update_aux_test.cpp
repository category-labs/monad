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
#include <category/async/util.hpp>
#include <category/core/assert.h>
#include <category/core/detail/start_lifetime_as_polyfill.hpp>
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>
#include <category/mpt/detail/db_metadata.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/util.hpp>

#include <gtest/gtest.h>

#include <atomic>
#include <csignal>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <memory>
#include <span>
#include <stop_token>
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
        aux_writer.metadata_ctx().append_root_offset(start_offset);
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
        aux_writer.metadata_ctx().append_root_offset(end_offset);
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
    monad::async::storage_pool::creation_flags flags;
    flags.num_cnv_chunks = 5;
    {
        // Create storage pool with 5 cnv chunks: 1 for metadata, 4 for
        // ring_a at init (ring_b has 0 chunks until secondary activates).
        monad::async::storage_pool pool(
            std::span{&filename, 1},
            monad::async::storage_pool::mode::truncate,
            flags);
        EXPECT_EQ(pool.chunks(monad::async::storage_pool::cnv), 5);

        monad::async::AsyncIO testio(pool, testbuf);
        monad::mpt::UpdateAux const aux(testio);

        EXPECT_EQ(
            aux.metadata_ctx().main()->root_offsets.storage_.cnv_chunks_len, 4);
        EXPECT_EQ(
            aux.metadata_ctx()
                .main()
                ->secondary_timeline.storage_.cnv_chunks_len,
            0);
        EXPECT_EQ(aux.metadata_ctx().root_offsets().capacity(), 2ULL << 25);
    }
    {
        // reopen storage_pool
        monad::async::storage_pool pool(
            std::span{&filename, 1},
            monad::async::storage_pool::mode::open_existing,
            flags);
        EXPECT_EQ(pool.chunks(monad::async::storage_pool::cnv), 5);
        monad::async::AsyncIO testio(pool, testbuf);
        monad::mpt::UpdateAux const aux(testio);
        EXPECT_EQ(
            aux.metadata_ctx().main()->root_offsets.storage_.cnv_chunks_len, 4);
        EXPECT_EQ(
            aux.metadata_ctx()
                .main()
                ->secondary_timeline.storage_.cnv_chunks_len,
            0);
        EXPECT_EQ(aux.metadata_ctx().root_offsets().capacity(), 2ULL << 25);
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
            aux.metadata_ctx()
                .main()
                ->secondary_timeline.storage_.cnv_chunks_len,
            0u);
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

// Simulates opening a DB created by pre-dual-timeline code (MONAD007), whose
// future_variables_unused region — now overlapping secondary_timeline — was
// filled with 0xff. On reopen the constructor must rewrite the magic and zero
// the header so the secondary timeline reads as inactive.
// Byte-level test for the MONAD007 -> MONAD008 layout-shift migration.
// MONAD008 shrank root_offsets_ring_t::SIZE_ from 65536 to 32, moving
// sizeof(db_metadata) from 528512 to 4480. Any real MONAD007 pool has
// chunk_info[], the list triple, and the db_offsets + consensus fields
// at byte offsets that the MONAD008 layout no longer uses. The ctor's
// migration must relocate those blocks before downstream code reads
// through the new offsets.
//
// This test writes a real MONAD007 layout directly to cnv chunk 0 (both
// copies), opens a DbMetadataContext, and asserts that survivable
// fields (consensus versions, cnv_chunks list, list triple, chunk_info
// entries) landed at their MONAD008 offsets with the right values and
// that new-in-MONAD008 fields initialised to their idle state.
TEST(update_aux_test, migrates_monad007_layout_to_monad008)
{
    using monad::mpt::detail::db_metadata;
    static constexpr size_t MONAD007_DB_METADATA_SIZE = 528512;
    static constexpr size_t MONAD007_DB_OFFSETS_OFFSET = 524328;
    static constexpr size_t MONAD007_LIST_TRIPLE_OFFSET = 528488;

    monad::async::storage_pool pool(monad::async::use_anonymous_inode_tag{});

    // Values that must survive the migration with bit-for-bit fidelity.
    uint64_t const test_history_length = 12345;
    uint64_t const test_latest_finalized = 42;
    uint64_t const test_latest_verified = 41;
    uint64_t const test_latest_voted = 40;
    uint64_t const test_latest_proposed = 43;
    uint64_t const test_capacity_in_free_list = 1'000'000;
    uint32_t const test_cnv_chunks_len = 2;
    uint32_t const test_cnv_chunk_id_0 = 1;
    uint32_t const test_cnv_chunk_id_1 = 2;
    uint32_t const test_free_list_begin = 5;
    uint32_t const test_free_list_end = 7;
    uint32_t const test_chunk_count = static_cast<uint32_t>(
        pool.chunks(monad::async::storage_pool::seq) +
        pool.chunks(monad::async::storage_pool::cnv));

    auto &cnv_chunk = pool.chunk(monad::async::storage_pool::cnv, 0);
    auto const [write_fd, base_offset] = cnv_chunk.write_fd(0);
    auto const half_capacity = cnv_chunk.capacity() / 2;

    auto const build_monad007_buffer = [&] {
        std::vector<uint8_t> buf(
            MONAD007_DB_METADATA_SIZE +
                size_t(test_chunk_count) * sizeof(db_metadata::chunk_info_t),
            0);
        // magic
        memcpy(
            buf.data(),
            db_metadata::PREVIOUS_MAGIC,
            db_metadata::MAGIC_STRING_LEN);
        // chunk_info_count bitfield (20 low bits)
        uint64_t const bitfield =
            static_cast<uint64_t>(test_chunk_count) & 0xfffffULL;
        memcpy(buf.data() + 8, &bitfield, 8);
        // capacity_in_free_list
        memcpy(buf.data() + 16, &test_capacity_in_free_list, 8);
        // root_offsets: version_lower_bound_ and next_version_ both 0
        // (buf is zeroed). storage_.high_bits_all_set = -1,
        // storage_.cnv_chunks_len = test_cnv_chunks_len.
        uint32_t const high_bits_all_set = uint32_t(-1);
        memcpy(buf.data() + 40, &high_bits_all_set, 4);
        memcpy(buf.data() + 44, &test_cnv_chunks_len, 4);
        // cnv_chunks[0] + [1] populated; the rest of the huge
        // MONAD007 cnv_chunks[] array filled with 0xff as MONAD007 did.
        memcpy(buf.data() + 48, &high_bits_all_set, 4);
        memcpy(buf.data() + 52, &test_cnv_chunk_id_0, 4);
        memcpy(buf.data() + 56, &high_bits_all_set, 4);
        memcpy(buf.data() + 60, &test_cnv_chunk_id_1, 4);
        memset(buf.data() + 64, 0xff, MONAD007_DB_OFFSETS_OFFSET - 64);
        // db_offsets at 524328 (16 bytes) — leave as zero.
        // history_length at 524344, then finalized/verified/voted/proposed.
        memcpy(buf.data() + 524344, &test_history_length, 8);
        memcpy(buf.data() + 524352, &test_latest_finalized, 8);
        memcpy(buf.data() + 524360, &test_latest_verified, 8);
        memcpy(buf.data() + 524368, &test_latest_voted, 8);
        memcpy(buf.data() + 524376, &test_latest_proposed, 8);
        // auto_expire_version at 524384 — zero. block_ids at 524392,
        // 524424 — zero. future_variables_unused 524456..528488: 0xff
        // (MONAD007 convention).
        memset(buf.data() + 524456, 0xff, MONAD007_LIST_TRIPLE_OFFSET - 524456);
        // free_list (begin, end) at MONAD007_LIST_TRIPLE_OFFSET.
        memcpy(
            buf.data() + MONAD007_LIST_TRIPLE_OFFSET, &test_free_list_begin, 4);
        memcpy(
            buf.data() + MONAD007_LIST_TRIPLE_OFFSET + 4,
            &test_free_list_end,
            4);
        // fast_list and slow_list (begin=UINT32_MAX, end=UINT32_MAX —
        // empty).
        uint32_t const invalid = UINT32_MAX;
        memcpy(buf.data() + MONAD007_LIST_TRIPLE_OFFSET + 8, &invalid, 4);
        memcpy(buf.data() + MONAD007_LIST_TRIPLE_OFFSET + 12, &invalid, 4);
        memcpy(buf.data() + MONAD007_LIST_TRIPLE_OFFSET + 16, &invalid, 4);
        memcpy(buf.data() + MONAD007_LIST_TRIPLE_OFFSET + 20, &invalid, 4);
        // chunk_info[] left at zero — valid, means all INVALID_CHUNK_IDs
        // except encoded by convention; the test doesn't need to verify
        // specific values, just that the bytes survive the relocation.
        return buf;
    };
    auto const buffer = build_monad007_buffer();
    // Write to both copies on disk.
    for (unsigned copy_idx = 0; copy_idx < 2; copy_idx++) {
        ssize_t const written = ::pwrite(
            write_fd,
            buffer.data(),
            buffer.size(),
            off_t(base_offset) + off_t(copy_idx) * off_t(half_capacity));
        ASSERT_EQ(ssize_t(buffer.size()), written)
            << "pwrite of copy " << copy_idx << " failed";
    }

    // Open DB. Ctor should migrate both copies.
    {
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

        for (unsigned i = 0; i < 2; i++) {
            auto const *const m = ctx.main(i);
            EXPECT_EQ(
                0,
                memcmp(
                    m->magic,
                    db_metadata::MAGIC,
                    db_metadata::MAGIC_STRING_LEN))
                << "copy " << i << " magic should be migrated to MONAD008";
            // Root_offsets header stayed at the same byte offset across
            // layouts — the cnv_chunks_len cap + the first two chunk ids
            // must survive with no relocation needed.
            EXPECT_EQ(
                m->root_offsets.storage_.cnv_chunks_len, test_cnv_chunks_len);
            EXPECT_EQ(
                m->root_offsets.storage_.cnv_chunks[0].cnv_chunk_id,
                test_cnv_chunk_id_0);
            EXPECT_EQ(
                m->root_offsets.storage_.cnv_chunks[1].cnv_chunk_id,
                test_cnv_chunk_id_1);
            // Consensus fields relocated from offset 524344+ to 312+.
            EXPECT_EQ(m->history_length, test_history_length);
            EXPECT_EQ(m->latest_finalized_version, test_latest_finalized);
            EXPECT_EQ(m->latest_verified_version, test_latest_verified);
            EXPECT_EQ(m->latest_voted_version, test_latest_voted);
            EXPECT_EQ(m->latest_proposed_version, test_latest_proposed);
            // List triple relocated from offset 528488 to 4456.
            EXPECT_EQ(m->free_list.begin, test_free_list_begin);
            EXPECT_EQ(m->free_list.end, test_free_list_end);
            EXPECT_EQ(m->fast_list.begin, UINT32_MAX);
            EXPECT_EQ(m->fast_list.end, UINT32_MAX);
            EXPECT_EQ(m->slow_list.begin, UINT32_MAX);
            EXPECT_EQ(m->slow_list.end, UINT32_MAX);
            // New-in-MONAD008 fields must start at idle values
            // regardless of what was in the overlapping MONAD007 bytes
            // (the migration explicitly zeros them).
            EXPECT_EQ(m->secondary_timeline.version_lower_bound_, 0u);
            EXPECT_EQ(m->secondary_timeline.next_version_, 0u);
            EXPECT_EQ(m->secondary_timeline.storage_.cnv_chunks_len, 0u);
            EXPECT_EQ(m->primary_ring_idx, 0u);
            EXPECT_EQ(m->secondary_timeline_active_, 0u);
            EXPECT_EQ(m->shrink_grow_seq_ & 1u, 0u);
            EXPECT_EQ(
                m->pending_shrink_grow.op_kind, db_metadata::PENDING_OP_NONE);
        }
        EXPECT_FALSE(ctx.timeline_active(timeline_id::secondary));
        EXPECT_TRUE(ctx.timeline_active(timeline_id::primary));
    }
}

// Simulates a crash mid-migration: copy 0 finished migrating to MONAD008 in
// a prior run; copy 1 still tagged MONAD007 with 0xff padding. The magic-
// validation heal does nothing (copy 0 is valid), so the migration loop's
// per-copy branch is the path that actually fixes copy 1.
TEST(update_aux_test, migrates_monad007_resumes_after_partial_migration)
{
    monad::async::storage_pool pool(monad::async::use_anonymous_inode_tag{});
    using monad::mpt::detail::db_metadata;

    {
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

        // Corrupt copy 1 only. Copy 0 stays MONAD008, so on reopen the
        // magic-validation heal at the top of the ctor sees copy 0 as
        // valid and takes no action — the fix must come from the
        // per-copy migration loop.
        auto *const m1 = const_cast<db_metadata *>(aux.metadata_ctx().main(1));
        auto const g = m1->hold_dirty();
        memcpy(
            m1->magic,
            db_metadata::PREVIOUS_MAGIC,
            db_metadata::MAGIC_STRING_LEN);
        memset(&m1->secondary_timeline, 0xff, sizeof(m1->secondary_timeline));
        m1->primary_ring_idx = 0xff;
        m1->secondary_timeline_active_ = 0xff;
        memset(m1->reserved_timeline_, 0xff, sizeof(m1->reserved_timeline_));
    }

    {
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

        for (unsigned i = 0; i < 2; i++) {
            auto const *const m = aux.metadata_ctx().main(i);
            EXPECT_EQ(
                0,
                memcmp(
                    m->magic,
                    db_metadata::MAGIC,
                    db_metadata::MAGIC_STRING_LEN))
                << "copy " << i << " magic should be MONAD008 after migration";
            EXPECT_EQ(m->secondary_timeline_active_, 0u);
            EXPECT_EQ(m->primary_ring_idx, 0u);
            EXPECT_EQ(m->secondary_timeline.next_version_, 0u);
            EXPECT_EQ(m->secondary_timeline.version_lower_bound_, 0u);
            // These fields overlap MONAD007's 0xff padding. If migration
            // ever stops zeroing them, shrink_grow_seq_ goes odd (readers
            // spin) and pending_shrink_grow.op_kind goes nonzero (replay
            // hits MONAD_ABORT on reopen).
            EXPECT_EQ(m->shrink_grow_seq_ & 1u, 0u)
                << "copy " << i << " shrink_grow_seq_ must be even after "
                << "migration (was 0xff padding under MONAD007)";
            EXPECT_EQ(
                m->pending_shrink_grow.op_kind, db_metadata::PENDING_OP_NONE)
                << "copy " << i << " pending_shrink_grow.op_kind must be "
                << "NONE after migration";
        }
    }
}

TEST(update_aux_test, activate_deactivate_secondary)
{
    with_rw_aux([](UpdateAux &aux) {
        EXPECT_FALSE(
            aux.metadata_ctx().timeline_active(timeline_id::secondary));

        aux.activate_secondary_timeline(42);
        EXPECT_TRUE(aux.metadata_ctx().timeline_active(timeline_id::secondary));

        // Header fields set on the secondary role's physical ring. With
        // no prior promote, primary_ring_idx==0 so secondary routes to
        // ring_b (secondary_timeline).
        auto const *md = aux.metadata_ctx().main();
        EXPECT_EQ(md->primary_ring_idx, 0u);
        EXPECT_EQ(md->secondary_timeline.version_lower_bound_, 42u);
        EXPECT_EQ(md->secondary_timeline.next_version_, 42u);
        EXPECT_EQ(md->secondary_timeline_active_, 1u);

        aux.deactivate_secondary_timeline();
        EXPECT_FALSE(
            aux.metadata_ctx().timeline_active(timeline_id::secondary));
        EXPECT_EQ(md->secondary_timeline_active_, 0u);
    });
}

TEST(update_aux_test, activate_inherits_compaction_state_from_primary)
{
    with_rw_aux([](UpdateAux &aux) {
        // Primary's compaction state is the default after init
        auto const primary_before = aux.tl(timeline_id::primary);

        aux.activate_secondary_timeline(42);

        // Secondary must inherit primary's compaction state
        auto const &secondary = aux.tl(timeline_id::secondary);
        EXPECT_EQ(
            secondary.compact_offsets.fast,
            primary_before.compact_offsets.fast);
        EXPECT_EQ(
            secondary.compact_offsets.slow,
            primary_before.compact_offsets.slow);
        EXPECT_EQ(
            secondary.compact_offset_range_fast_,
            primary_before.compact_offset_range_fast_);
        EXPECT_EQ(
            secondary.compact_offset_range_slow_,
            primary_before.compact_offset_range_slow_);

        aux.deactivate_secondary_timeline();

        // After deactivation, secondary compaction state is reset to default
        timeline_compaction_state const default_state{};
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

        aux.activate_secondary_timeline(5);
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
        aux.activate_secondary_timeline(50);

        // Verify both metadata copies have matching secondary header
        auto ro0 = aux.metadata_ctx().root_offsets(timeline_id::secondary, 0);
        auto ro1 = aux.metadata_ctx().root_offsets(timeline_id::secondary, 1);
        EXPECT_EQ(ro0.max_version(), ro1.max_version());
        EXPECT_FALSE(ro0.empty());
        EXPECT_FALSE(ro1.empty());

        // Push a root and verify both copies
        chunk_offset_t const offset{3, 42};
        ro0.push(offset);
        ro1.push(offset);
        EXPECT_EQ(ro0[50].id, offset.id);
        EXPECT_EQ(ro1[50].id, offset.id);

        // Promote and verify both copies swapped
        aux.promote_secondary_to_primary();
        auto const new_pro0 =
            aux.metadata_ctx().root_offsets(timeline_id::primary, 0);
        auto const new_pro1 =
            aux.metadata_ctx().root_offsets(timeline_id::primary, 1);
        EXPECT_EQ(new_pro0.max_version(), new_pro1.max_version());
        EXPECT_EQ(new_pro0[50].id, offset.id);
        EXPECT_EQ(new_pro1[50].id, offset.id);

        aux.deactivate_secondary_timeline();
    });
}

TEST(update_aux_test, activate_at_version_zero)
{
    with_rw_aux([](UpdateAux &aux) {
        aux.activate_secondary_timeline(0);
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
        // First activation
        aux.activate_secondary_timeline(10);
        auto sro = aux.metadata_ctx().root_offsets(timeline_id::secondary);
        chunk_offset_t const first_offset{3, 100};
        sro.push(first_offset);
        EXPECT_EQ(sro[10].id, first_offset.id);
        aux.deactivate_secondary_timeline();

        // Reactivate at a different version
        aux.activate_secondary_timeline(20);
        EXPECT_TRUE(aux.metadata_ctx().timeline_active(timeline_id::secondary));

        // Old data should be wiped (ring re-initialized to INVALID_OFFSET)
        auto sro2 = aux.metadata_ctx().root_offsets(timeline_id::secondary);
        EXPECT_EQ(sro2[10], monad::async::INVALID_OFFSET)
            << "Stale data from first activation should be cleared";

        // New push works
        chunk_offset_t const second_offset{4, 200};
        sro2.push(second_offset);
        EXPECT_EQ(sro2[20].id, second_offset.id);

        aux.deactivate_secondary_timeline();
    });
}

TEST(update_aux_test, secondary_ring_initialized_to_invalid_offset_on_activate)
{
    with_rw_aux([](UpdateAux &aux) {
        // After activation, the secondary ring has been allocated chunks
        // (taken from the shrunk primary) and initialised to
        // INVALID_OFFSET by activate_secondary_header.
        aux.activate_secondary_timeline(0);
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
        aux.activate_secondary_timeline(10);

        // Push a root offset to the secondary ring
        auto ro = aux.metadata_ctx().root_offsets(timeline_id::secondary);
        EXPECT_EQ(ro.max_version(), 9u); // next_version(10) - 1

        chunk_offset_t const test_offset{3, 42};
        ro.push(test_offset);
        EXPECT_EQ(ro.max_version(), 10u);
        EXPECT_EQ(ro[10].id, test_offset.id);
        EXPECT_EQ(ro[10].offset, test_offset.offset);

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

        // Activate secondary and push a root at version 5
        aux.activate_secondary_timeline(5);
        auto sro = aux.metadata_ctx().root_offsets(timeline_id::secondary);
        chunk_offset_t const secondary_offset{2, 200};
        sro.push(secondary_offset);
        EXPECT_EQ(sro.max_version(), 5u);

        // Promote
        aux.promote_secondary_to_primary();

        // After promotion: what was secondary is now primary
        auto const new_pro =
            aux.metadata_ctx().root_offsets(timeline_id::primary);
        EXPECT_EQ(new_pro.max_version(), 5u);
        EXPECT_EQ(new_pro[5].id, secondary_offset.id);

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

        // Activate secondary at version 10
        aux.activate_secondary_timeline(10);
        EXPECT_EQ(
            aux.metadata_ctx().db_history_min_valid_version(
                timeline_id::secondary),
            10u);
        // Secondary max_version is next_version_ - 1 = 9 (no pushes yet)
        EXPECT_EQ(
            aux.metadata_ctx().db_history_max_version(timeline_id::secondary),
            9u);

        // Push to secondary
        auto sro = aux.metadata_ctx().root_offsets(timeline_id::secondary);
        sro.push(chunk_offset_t{1, 0});
        EXPECT_EQ(
            aux.metadata_ctx().db_history_max_version(timeline_id::secondary),
            10u);

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
    flags.num_cnv_chunks = 5;

    chunk_offset_t const primary_before{1, 0};
    chunk_offset_t const secondary_before{2, 0};

    // Session 1: init pool, activate + push to both rings, promote.
    {
        monad::async::storage_pool pool(
            std::span{&filename, 1},
            monad::async::storage_pool::mode::truncate,
            flags);
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
        ctx.activate_secondary_header(5);
        ctx.root_offsets(timeline_id::secondary).push(secondary_before);
        ctx.promote_secondary_to_primary_header();

        EXPECT_EQ(ctx.primary_ring_idx(), 1u);
        auto const new_pro = ctx.root_offsets(timeline_id::primary);
        EXPECT_EQ(new_pro[5].id, secondary_before.id);
    }

    // Session 2: reopen. primary_ring_idx must survive.
    {
        monad::async::storage_pool pool(
            std::span{&filename, 1},
            monad::async::storage_pool::mode::open_existing,
            flags);
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
        EXPECT_EQ(new_pro.max_version(), 5u);
        EXPECT_EQ(new_pro[5].id, secondary_before.id);

        auto const new_sro = ctx.root_offsets(timeline_id::secondary);
        EXPECT_EQ(new_sro.max_version(), 0u);
        EXPECT_EQ(new_sro[0].id, primary_before.id);
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
    flags.num_cnv_chunks = 5;

    // Session 1: init pool; stamp pending activate flag manually (as if a
    // crash happened right after set_pending_shrink_grow_ + msync but
    // before do_activate_secondary_body_ started).
    uint32_t target_chunks = 0;
    {
        monad::async::storage_pool pool(
            std::span{&filename, 1},
            monad::async::storage_pool::mode::truncate,
            flags);
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
        auto const old_chunks =
            ctx.main()->root_offsets.storage_.cnv_chunks_len;
        ASSERT_GE(old_chunks, 2u);
        ASSERT_EQ(old_chunks & (old_chunks - 1), 0u);
        target_chunks = old_chunks / 2;

        // Stamp pending flag on both copies under hold_dirty. Also bump
        // shrink_grow_seq_ odd on both to match the real code path.
        for (unsigned which = 0; which < 2; which++) {
            auto *const m = const_cast<db_metadata *>(ctx.main(which));
            auto const g = m->hold_dirty();
            m->pending_shrink_grow.op_kind = db_metadata::PENDING_OP_ACTIVATE;
            m->pending_shrink_grow.target_primary_chunks = target_chunks;
            m->pending_shrink_grow.fork_version = 42;
            monad::start_lifetime_as<std::atomic<uint64_t>>(
                &m->shrink_grow_seq_)
                ->fetch_add(1, std::memory_order_acq_rel);
        }
        // Dtor runs: DbMetadataContext unmaps without clearing the flag,
        // simulating a crash before clear_pending_shrink_grow_.
    }

    // Session 2: reopen. Replay must finish the activate.
    {
        monad::async::storage_pool pool(
            std::span{&filename, 1},
            monad::async::storage_pool::mode::open_existing,
            flags);
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
            // seq should be even (replay's clear_pending_shrink_grow_
            // bumps it back).
            EXPECT_EQ(m->shrink_grow_seq_ & 1u, 0u);
        }
        // Activate completed: primary shrunk to target, secondary active.
        EXPECT_TRUE(ctx.timeline_active(timeline_id::secondary));
        EXPECT_EQ(
            ctx.main()->root_offsets.storage_.cnv_chunks_len, target_chunks);
        EXPECT_EQ(
            ctx.main()->secondary_timeline.storage_.cnv_chunks_len,
            target_chunks);
        EXPECT_EQ(ctx.main()->secondary_timeline.version_lower_bound_, 42u);
        EXPECT_EQ(ctx.main()->secondary_timeline.next_version_, 42u);
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
    flags.num_cnv_chunks = 5;

    uint32_t target_chunks = 0;

    {
        monad::async::storage_pool pool(
            std::span{&filename, 1},
            monad::async::storage_pool::mode::truncate,
            flags);
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

        target_chunks = ctx.main()->root_offsets.storage_.cnv_chunks_len / 2;

        // Fully activate. No subsequent pushes — in production the
        // modelled crash happens while the writer is still inside
        // activate_secondary_header (post-body-sync, pre-flag-clear-
        // msync), so no push has ever touched the post-activate state.
        ctx.activate_secondary_header(7);

        // Stamp the pending flag back on — simulates a crash after the
        // body finished but before the flag-clear msync completed.
        for (unsigned which = 0; which < 2; which++) {
            auto *const m = const_cast<db_metadata *>(ctx.main(which));
            auto const g = m->hold_dirty();
            m->pending_shrink_grow.op_kind = db_metadata::PENDING_OP_ACTIVATE;
            m->pending_shrink_grow.target_primary_chunks = target_chunks;
            m->pending_shrink_grow.fork_version = 7;
            monad::start_lifetime_as<std::atomic<uint64_t>>(
                &m->shrink_grow_seq_)
                ->fetch_add(1, std::memory_order_acq_rel);
        }
    }

    {
        monad::async::storage_pool pool(
            std::span{&filename, 1},
            monad::async::storage_pool::mode::open_existing,
            flags);
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
            EXPECT_EQ(m->shrink_grow_seq_ & 1u, 0u);
        }
        EXPECT_TRUE(ctx.timeline_active(timeline_id::secondary));
        EXPECT_EQ(
            ctx.main()->root_offsets.storage_.cnv_chunks_len, target_chunks);
        EXPECT_EQ(
            ctx.main()->secondary_timeline.storage_.cnv_chunks_len,
            target_chunks);
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
    flags.num_cnv_chunks = 5;

    uint32_t target_chunks = 0;
    {
        monad::async::storage_pool pool(
            std::span{&filename, 1},
            monad::async::storage_pool::mode::truncate,
            flags);
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

        ctx.activate_secondary_header(10);
        auto const primary_after_activate =
            ctx.main()->root_offsets.storage_.cnv_chunks_len;
        auto const secondary_after_activate =
            ctx.main()->secondary_timeline.storage_.cnv_chunks_len;
        target_chunks = primary_after_activate + secondary_after_activate;

        // Stamp pending deactivate flag on both copies.
        for (unsigned which = 0; which < 2; which++) {
            auto *const m = const_cast<db_metadata *>(ctx.main(which));
            auto const g = m->hold_dirty();
            m->pending_shrink_grow.op_kind = db_metadata::PENDING_OP_DEACTIVATE;
            m->pending_shrink_grow.target_primary_chunks = target_chunks;
            m->pending_shrink_grow.fork_version = 0;
            monad::start_lifetime_as<std::atomic<uint64_t>>(
                &m->shrink_grow_seq_)
                ->fetch_add(1, std::memory_order_acq_rel);
        }
    }

    {
        monad::async::storage_pool pool(
            std::span{&filename, 1},
            monad::async::storage_pool::mode::open_existing,
            flags);
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
            EXPECT_EQ(m->shrink_grow_seq_ & 1u, 0u);
        }
        EXPECT_FALSE(ctx.timeline_active(timeline_id::secondary));
        EXPECT_EQ(
            ctx.main()->root_offsets.storage_.cnv_chunks_len, target_chunks);
        EXPECT_EQ(ctx.main()->secondary_timeline.storage_.cnv_chunks_len, 0u);
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
    flags.num_cnv_chunks = 5; // 4 ring chunks → activate shrinks to 2

    uint32_t target_chunks = 0;
    uint32_t already_moved_id = uint32_t(-1);
    uint32_t not_yet_moved_id = uint32_t(-1);
    {
        monad::async::storage_pool pool(
            std::span{&filename, 1},
            monad::async::storage_pool::mode::truncate,
            flags);
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

        auto const old_chunks =
            ctx.main()->root_offsets.storage_.cnv_chunks_len;
        ASSERT_EQ(old_chunks, 4u);
        target_chunks = old_chunks / 2;
        ASSERT_EQ(target_chunks, 2u);

        // Snapshot which chunks activate would move (the second half of
        // the primary ring's cnv_chunks list).
        already_moved_id =
            ctx.main()
                ->root_offsets.storage_.cnv_chunks[target_chunks + 0]
                .cnv_chunk_id;
        not_yet_moved_id =
            ctx.main()
                ->root_offsets.storage_.cnv_chunks[target_chunks + 1]
                .cnv_chunk_id;
        ASSERT_NE(already_moved_id, uint32_t(-1));
        ASSERT_NE(not_yet_moved_id, uint32_t(-1));
        ASSERT_NE(already_moved_id, not_yet_moved_id);

        for (unsigned which = 0; which < 2; which++) {
            auto *const m = const_cast<db_metadata *>(ctx.main(which));
            auto const g = m->hold_dirty();
            m->pending_shrink_grow.op_kind = db_metadata::PENDING_OP_ACTIVATE;
            m->pending_shrink_grow.target_primary_chunks = target_chunks;
            m->pending_shrink_grow.fork_version = 99;
            monad::start_lifetime_as<std::atomic<uint64_t>>(
                &m->shrink_grow_seq_)
                ->fetch_add(1, std::memory_order_acq_rel);

            // Hand-apply the first move only (primary→secondary for k=0).
            // Leave k=1 at pristine pre-move state.
            auto &pstore = m->root_offsets.storage_;
            auto &sstore = m->secondary_timeline.storage_;
            sstore.cnv_chunks[0].high_bits_all_set = uint32_t(-1);
            sstore.cnv_chunks[0].cnv_chunk_id = already_moved_id;
            pstore.cnv_chunks[target_chunks + 0].cnv_chunk_id = uint32_t(-1);
        }
    }

    {
        monad::async::storage_pool pool(
            std::span{&filename, 1},
            monad::async::storage_pool::mode::open_existing,
            flags);
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
            EXPECT_EQ(m->shrink_grow_seq_ & 1u, 0u);
            auto const &pstore = m->root_offsets.storage_;
            auto const &sstore = m->secondary_timeline.storage_;

            // The already-moved entry survived — the idempotency guard's
            // "skip if destination already has a valid id" branch didn't
            // re-move it or wipe it.
            EXPECT_EQ(sstore.cnv_chunks[0].cnv_chunk_id, already_moved_id);
            // The not-yet-moved entry was completed by replay.
            EXPECT_EQ(sstore.cnv_chunks[1].cnv_chunk_id, not_yet_moved_id);
            // Source slots on primary are cleared.
            EXPECT_EQ(
                pstore.cnv_chunks[target_chunks + 0].cnv_chunk_id,
                uint32_t(-1));
            EXPECT_EQ(
                pstore.cnv_chunks[target_chunks + 1].cnv_chunk_id,
                uint32_t(-1));
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
    flags.num_cnv_chunks = 5;

    chunk_offset_t const pushed{7, 12345};
    uint32_t target_chunks = 0;
    {
        monad::async::storage_pool pool(
            std::span{&filename, 1},
            monad::async::storage_pool::mode::truncate,
            flags);
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

        target_chunks = ctx.main()->root_offsets.storage_.cnv_chunks_len / 2;
        for (unsigned which = 0; which < 2; which++) {
            auto *const m = const_cast<db_metadata *>(ctx.main(which));
            auto const g = m->hold_dirty();
            m->pending_shrink_grow.op_kind = db_metadata::PENDING_OP_ACTIVATE;
            m->pending_shrink_grow.target_primary_chunks = target_chunks;
            m->pending_shrink_grow.fork_version = 77;
            monad::start_lifetime_as<std::atomic<uint64_t>>(
                &m->shrink_grow_seq_)
                ->fetch_add(1, std::memory_order_acq_rel);
        }
    }

    {
        monad::async::storage_pool pool(
            std::span{&filename, 1},
            monad::async::storage_pool::mode::open_existing,
            flags);
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
        EXPECT_EQ(
            ctx.main()->root_offsets.storage_.cnv_chunks_len, target_chunks);

        // The pushed offset at version 0 survived replay.
        EXPECT_EQ(ctx.root_offsets(timeline_id::primary)[0].id, pushed.id);
        EXPECT_EQ(ctx.root_offsets(timeline_id::primary).max_version(), 0u);
    }

    remove(filename);
}

// Replay recovers from a crash that landed between the two per-copy
// stamp scopes in set_pending_shrink_grow_: copy 0 has the flag set
// and shrink_grow_seq_ bumped to odd, copy 1 is still pristine. Both
// copies are clean (neither dirty), so dirty-bit recovery does
// nothing. Replay must still fire (because copy 0 carries a pending
// op) and must leave both copies with shrink_grow_seq_ even —
// otherwise copy 1 could be durably odd, and a later db_copy from
// copy 1 would wedge readers on the seqlock spin.
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
    flags.num_cnv_chunks = 5;

    uint32_t target_chunks = 0;
    uint64_t copy1_seq_before = 0;
    {
        monad::async::storage_pool pool(
            std::span{&filename, 1},
            monad::async::storage_pool::mode::truncate,
            flags);
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

        target_chunks = ctx.main()->root_offsets.storage_.cnv_chunks_len / 2;
        copy1_seq_before = ctx.main(1)->shrink_grow_seq_;

        // Stamp pending + bump seq on copy 0 ONLY. Leave copy 1 entirely
        // unmodified (op_kind == NONE, seq even).
        auto *const m0 = const_cast<db_metadata *>(ctx.main(0));
        auto const g0 = m0->hold_dirty();
        m0->pending_shrink_grow.op_kind = db_metadata::PENDING_OP_ACTIVATE;
        m0->pending_shrink_grow.target_primary_chunks = target_chunks;
        m0->pending_shrink_grow.fork_version = 55;
        monad::start_lifetime_as<std::atomic<uint64_t>>(&m0->shrink_grow_seq_)
            ->fetch_add(1, std::memory_order_acq_rel);
        // Sanity: copy 0 now has seq odd, copy 1 still even.
        ASSERT_EQ(ctx.main(0)->shrink_grow_seq_ & 1u, 1u);
        ASSERT_EQ(ctx.main(1)->shrink_grow_seq_ & 1u, 0u);
    }

    {
        monad::async::storage_pool pool(
            std::span{&filename, 1},
            monad::async::storage_pool::mode::open_existing,
            flags);
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
            EXPECT_EQ(m->shrink_grow_seq_ & 1u, 0u)
                << "copy " << which
                << " shrink_grow_seq_ must be even after replay — the "
                   "clear path must normalise parity regardless of which "
                   "copies had the seq bumped during stamp";
        }
        // Copy 1's seq must have advanced strictly (generation bump),
        // so a reader that had observed it pre-crash would see the
        // change.
        EXPECT_GT(ctx.main(1)->shrink_grow_seq_, copy1_seq_before);
        EXPECT_TRUE(ctx.timeline_active(timeline_id::secondary));
    }

    remove(filename);
}

TEST(update_aux_test, version_is_valid_ondisk_per_timeline)
{
    with_rw_aux([](UpdateAux &aux) {
        // Push to primary at version 0
        auto pro = aux.metadata_ctx().root_offsets(timeline_id::primary);
        pro.push(chunk_offset_t{1, 0});
        EXPECT_TRUE(aux.metadata_ctx().version_is_valid_ondisk(
            0, timeline_id::primary));
        EXPECT_FALSE(aux.metadata_ctx().version_is_valid_ondisk(
            1, timeline_id::primary));

        // Activate secondary at version 5
        aux.activate_secondary_timeline(5);
        auto sro = aux.metadata_ctx().root_offsets(timeline_id::secondary);
        sro.push(chunk_offset_t{2, 0});

        // Version 5 valid on secondary, not on primary
        EXPECT_TRUE(aux.metadata_ctx().version_is_valid_ondisk(
            5, timeline_id::secondary));
        EXPECT_FALSE(aux.metadata_ctx().version_is_valid_ondisk(
            5, timeline_id::primary));

        // Version 0 valid on primary, not on secondary
        EXPECT_TRUE(aux.metadata_ctx().version_is_valid_ondisk(
            0, timeline_id::primary));
        EXPECT_FALSE(aux.metadata_ctx().version_is_valid_ondisk(
            0, timeline_id::secondary));

        aux.deactivate_secondary_timeline();
    });
}
