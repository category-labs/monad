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

#include "add_devices_test_util.hpp"
#include "db_metadata_test_access.hpp"

#include <category/async/config.hpp>
#include <category/async/detail/scope_polyfill.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/mpt/config.hpp>

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <vector>

#include <unistd.h>

using namespace MONAD_ASYNC_NAMESPACE;
using namespace MONAD_MPT_NAMESPACE;
using add_devices_test::BLKSIZE;
using add_devices_test::create_temp_file;
using add_devices_test::free_list_ids;
using add_devices_test::opened_db;

TEST(add_devices, grows_chunk_info_and_free_list)
{
    auto const dev0 = create_temp_file(20 * BLKSIZE);
    auto const dev1 = create_temp_file(10 * BLKSIZE);
    auto const undevs = monad::make_scope_exit([&]() noexcept {
        std::filesystem::remove(dev0);
        std::filesystem::remove(dev1);
    });
    std::filesystem::path const one[] = {dev0};
    std::filesystem::path const both[] = {dev0, dev1};

    uint32_t before_count = 0;
    uint64_t before_capacity = 0;
    std::vector<uint32_t> before_free;
    {
        opened_db db{one, storage_pool::mode::create_if_needed};
        auto const *m = db.aux.metadata_ctx().main();
        before_count = static_cast<uint32_t>(m->chunk_info_count);
        before_capacity = m->capacity_in_free_list;
        before_free = free_list_ids(m);
    }
    ASSERT_GT(before_count, 0u);

    opened_db db{both, storage_pool::mode::add_devices};
    auto const *m0 = db.aux.metadata_ctx().main(0);
    auto const *m1 = db.aux.metadata_ctx().main(1);
    auto const after_count = static_cast<uint32_t>(m0->chunk_info_count);
    EXPECT_EQ(after_count, db.io.chunk_count());
    EXPECT_GT(after_count, before_count);
    EXPECT_EQ(uint32_t(m1->chunk_info_count), after_count);

    // The old free-list order is preserved and the new ids follow it, in
    // ascending order, at the tail.
    auto const after_free = free_list_ids(m0);
    ASSERT_EQ(
        after_free.size(), before_free.size() + (after_count - before_count));
    for (size_t n = 0; n < before_free.size(); n++) {
        EXPECT_EQ(after_free[n], before_free[n]) << "free slot " << n;
    }
    for (uint32_t n = before_count; n < after_count; n++) {
        EXPECT_EQ(after_free[before_free.size() + (n - before_count)], n);
    }
    EXPECT_EQ(free_list_ids(m1), after_free);

    // Insertion counts stay monotone across the splice point, which is what
    // chunk_list_and_age relies on.
    for (size_t n = 1; n < after_free.size(); n++) {
        EXPECT_EQ(
            uint32_t(m0->at(after_free[n])->insertion_count()),
            uint32_t(m0->at(after_free[n - 1])->insertion_count()) + 1)
            << "free slot " << n;
    }

    // Free capacity grew by exactly the new chunks' capacity.
    uint64_t added = 0;
    for (uint32_t n = before_count; n < after_count; n++) {
        added += db.pool.chunk(storage_pool::seq, n).capacity();
    }
    EXPECT_EQ(m0->capacity_in_free_list, before_capacity + added);
    EXPECT_EQ(m1->capacity_in_free_list, before_capacity + added);
    EXPECT_EQ(
        m0->pending_shrink_grow.op_kind,
        MONAD_MPT_NAMESPACE::detail::db_metadata::PENDING_OP_NONE);
}

TEST(add_devices, reopening_a_grown_pool_changes_nothing)
{
    auto const dev0 = create_temp_file(20 * BLKSIZE);
    auto const dev1 = create_temp_file(10 * BLKSIZE);
    auto const undevs = monad::make_scope_exit([&]() noexcept {
        std::filesystem::remove(dev0);
        std::filesystem::remove(dev1);
    });
    std::filesystem::path const one[] = {dev0};
    std::filesystem::path const both[] = {dev0, dev1};
    {
        opened_db const db{one, storage_pool::mode::create_if_needed};
    }

    uint32_t count = 0;
    uint64_t capacity = 0;
    std::vector<uint32_t> free_ids;
    {
        opened_db db{both, storage_pool::mode::add_devices};
        auto const *m = db.aux.metadata_ctx().main();
        count = static_cast<uint32_t>(m->chunk_info_count);
        capacity = m->capacity_in_free_list;
        free_ids = free_list_ids(m);
    }
    opened_db db{both, storage_pool::mode::open_existing};
    auto const *m = db.aux.metadata_ctx().main();
    EXPECT_EQ(uint32_t(m->chunk_info_count), count);
    EXPECT_EQ(m->capacity_in_free_list, capacity);
    EXPECT_EQ(free_list_ids(m), free_ids);
}

// Reproduces the crash window between do_add_devices_body_'s two per-copy
// scopes: pending record stamped, copy 0 grown, copy 1 not, neither copy
// dirty. Built by raw file I/O on cnv chunk 0 rather than by driving
// DbMetadataContext, whose constructor always leaves the two copies agreeing.
// Same technique as provision_monad007_pool in cli_tool_test.cpp.
TEST(add_devices, interrupted_growth_replays_on_reopen)
{
    auto const dev0 = create_temp_file(20 * BLKSIZE);
    auto const dev1 = create_temp_file(10 * BLKSIZE);
    auto const undevs = monad::make_scope_exit([&]() noexcept {
        std::filesystem::remove(dev0);
        std::filesystem::remove(dev1);
    });
    std::filesystem::path const one[] = {dev0};
    std::filesystem::path const both[] = {dev0, dev1};

    // cnv chunk 0 geometry, and copy 1's pre-growth bytes.
    file_offset_t base_offset = 0;
    file_offset_t half_capacity = 0;
    std::vector<std::byte> saved_copy1;
    size_t pre_growth_count = 0;
    {
        opened_db db{one, storage_pool::mode::create_if_needed};
        auto &cnv = db.pool.chunk(storage_pool::cnv, 0);
        auto const fdr = cnv.read_fd();
        auto const fdw = cnv.write_fd(0);
        ASSERT_EQ(fdr.second, fdw.second)
            << "read/write fds disagree on cnv chunk 0's base offset; the "
               "pread/pwrite geometry below would be silently wrong";
        base_offset = fdr.second;
        half_capacity = cnv.capacity() / 2;
        ASSERT_GT(half_capacity, 0u);
        pre_growth_count = db.aux.metadata_ctx().main()->chunk_info_count;
        saved_copy1.resize(static_cast<size_t>(half_capacity));
        auto const got = ::pread(
            fdr.first,
            saved_copy1.data(),
            saved_copy1.size(),
            static_cast<off_t>(base_offset + half_capacity));
        ASSERT_EQ(got, ssize_t(saved_copy1.size()));
    }

    // Complete the add so copy 0 is fully grown and the pool is joined.
    size_t grown_count = 0;
    {
        opened_db db{both, storage_pool::mode::add_devices};
        grown_count = db.aux.metadata_ctx().main()->chunk_info_count;
    }
    ASSERT_GT(grown_count, pre_growth_count);

    // Roll copy 1 back to its pre-growth bytes and stamp the pending record
    // into both copies, clean.
    {
        storage_pool pool{both, storage_pool::mode::open_existing};
        auto &cnv = pool.chunk(storage_pool::cnv, 0);
        auto const fdw = cnv.write_fd(0);
        ASSERT_EQ(
            ssize_t(saved_copy1.size()),
            ::pwrite(
                fdw.first,
                saved_copy1.data(),
                saved_copy1.size(),
                static_cast<off_t>(base_offset + half_capacity)));
        MONAD_MPT_NAMESPACE::detail::db_metadata::pending_shrink_grow_t const
            pending{
                MONAD_MPT_NAMESPACE::detail::db_metadata::
                    PENDING_OP_ADD_DEVICES,
                static_cast<uint32_t>(grown_count)};
        for (unsigned which = 0; which < 2; which++) {
            ASSERT_EQ(
                ssize_t(sizeof(pending)),
                ::pwrite(
                    fdw.first,
                    &pending,
                    sizeof(pending),
                    static_cast<off_t>(
                        base_offset + which * half_capacity +
                        offsetof(
                            MONAD_MPT_NAMESPACE::detail::db_metadata,
                            pending_shrink_grow))));
        }
        ASSERT_EQ(0, ::fsync(fdw.first));

        // Confirm the crash window was actually built, by reading back what
        // is genuinely on disk rather than through a mapped
        // DbMetadataContext. If this doesn't hold, the reopen below would
        // converge trivially (or not exercise replay at all) and the
        // assertions past it would pass vacuously.
        uint64_t copy1_header_word = 0;
        ASSERT_EQ(
            ssize_t(sizeof(copy1_header_word)),
            ::pread(
                fdw.first,
                &copy1_header_word,
                sizeof(copy1_header_word),
                static_cast<off_t>(
                    base_offset + half_capacity +
                    MONAD_MPT_NAMESPACE::detail::db_metadata::
                        MAGIC_STRING_LEN)));
        ASSERT_EQ(copy1_header_word & 0xfffffU, uint64_t(pre_growth_count))
            << "copy 1's chunk_info_count was not rolled back; the crash "
               "window was not built";
        for (unsigned which = 0; which < 2; which++) {
            MONAD_MPT_NAMESPACE::detail::db_metadata::pending_shrink_grow_t
                readback_pending{};
            ASSERT_EQ(
                ssize_t(sizeof(readback_pending)),
                ::pread(
                    fdw.first,
                    &readback_pending,
                    sizeof(readback_pending),
                    static_cast<off_t>(
                        base_offset + which * half_capacity +
                        offsetof(
                            MONAD_MPT_NAMESPACE::detail::db_metadata,
                            pending_shrink_grow))));
            ASSERT_EQ(
                readback_pending.op_kind,
                uint32_t(MONAD_MPT_NAMESPACE::detail::db_metadata::
                             PENDING_OP_ADD_DEVICES))
                << "copy " << which << " does not carry the pending record";

            uint8_t dirty_byte = 0xff;
            ASSERT_EQ(
                ssize_t(sizeof(dirty_byte)),
                ::pread(
                    fdw.first,
                    &dirty_byte,
                    sizeof(dirty_byte),
                    static_cast<off_t>(
                        base_offset + which * half_capacity +
                        offsetof(
                            MONAD_MPT_NAMESPACE::detail::db_metadata,
                            capacity_in_free_list) -
                        1)));
            ASSERT_EQ(dirty_byte, 0u)
                << "copy " << which
                << " is dirty; dirty-bit recovery (not replay) would "
                   "resolve this window, defeating the point of the test";
        }
    }

    // Reopening must replay and converge both copies.
    opened_db db{both, storage_pool::mode::open_existing};
    auto const *m0 = db.aux.metadata_ctx().main(0);
    auto const *m1 = db.aux.metadata_ctx().main(1);
    EXPECT_EQ(uint32_t(m0->chunk_info_count), db.io.chunk_count());
    EXPECT_EQ(uint32_t(m1->chunk_info_count), db.io.chunk_count());
    EXPECT_EQ(m0->capacity_in_free_list, m1->capacity_in_free_list);
    EXPECT_EQ(free_list_ids(m0), free_list_ids(m1));
    EXPECT_EQ(
        m0->pending_shrink_grow.op_kind,
        MONAD_MPT_NAMESPACE::detail::db_metadata::PENDING_OP_NONE);
    EXPECT_EQ(
        m1->pending_shrink_grow.op_kind,
        MONAD_MPT_NAMESPACE::detail::db_metadata::PENDING_OP_NONE);
}

// An add interrupted between the storage layer's commit and the metadata
// growth -- the state add_devices_death_no_mode leaves behind -- is finished by
// re-running the same operation.
TEST(add_devices, rerun_finishes_a_pool_layer_only_join)
{
    auto const dev0 = create_temp_file(20 * BLKSIZE);
    auto const dev1 = create_temp_file(10 * BLKSIZE);
    auto const undevs = monad::make_scope_exit([&]() noexcept {
        std::filesystem::remove(dev0);
        std::filesystem::remove(dev1);
    });
    std::filesystem::path const one[] = {dev0};
    std::filesystem::path const both[] = {dev0, dev1};

    size_t pre_growth_count = 0;
    {
        opened_db db{one, storage_pool::mode::create_if_needed};
        pre_growth_count = db.aux.metadata_ctx().main()->chunk_info_count;
    }
    {
        storage_pool const pool{both, storage_pool::mode::add_devices};
    }

    opened_db db{both, storage_pool::mode::add_devices};
    auto const *m0 = db.aux.metadata_ctx().main(0);
    auto const *m1 = db.aux.metadata_ctx().main(1);
    EXPECT_GT(uint32_t(m0->chunk_info_count), pre_growth_count);
    EXPECT_EQ(uint32_t(m0->chunk_info_count), db.io.chunk_count());
    EXPECT_EQ(uint32_t(m1->chunk_info_count), db.io.chunk_count());
    EXPECT_EQ(free_list_ids(m0), free_list_ids(m1));
    EXPECT_EQ(m0->capacity_in_free_list, m1->capacity_in_free_list);
    EXPECT_EQ(
        m0->pending_shrink_grow.op_kind,
        MONAD_MPT_NAMESPACE::detail::db_metadata::PENDING_OP_NONE);
}

// The bounds are unit tested directly rather than by provisioning a pool of
// hundreds of gigabytes.
TEST(add_devices, chunk_info_bounds)
{
    // 4096 chunks at 8 bytes each on top of the MONAD007 header, inside a 1Mb
    // half-chunk: fits.
    MONAD_MPT_NAMESPACE::test::AddDevicesTestAccess::check_chunk_info_fits(
        4096, 1024 * 1024);
    ASSERT_DEATH(
        MONAD_MPT_NAMESPACE::test::AddDevicesTestAccess::check_chunk_info_fits(
            0x100000, 1 << 30),
        "20 bit chunk id space");
    ASSERT_DEATH(
        MONAD_MPT_NAMESPACE::test::AddDevicesTestAccess::check_chunk_info_fits(
            100000, 1024 * 1024),
        "conventional chunk 0 only provides");
}
