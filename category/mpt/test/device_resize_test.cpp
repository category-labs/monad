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

#include <category/async/config.hpp>
#include <category/async/detail/scope_polyfill.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/assert.h>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/mpt/config.hpp>
#include <category/mpt/detail/db_metadata.hpp>

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <vector>

#include <fcntl.h>
#include <unistd.h>

using namespace MONAD_ASYNC_NAMESPACE;
using namespace MONAD_MPT_NAMESPACE;
using add_devices_test::BLKSIZE;
using add_devices_test::create_temp_file;
using add_devices_test::opened_db;

namespace
{
    // Byte offset of device_sizes[index] within metadata copy `which`, from
    // the base of cnv chunk 0.
    off_t device_size_offset(
        file_offset_t const base_offset, file_offset_t const half_capacity,
        unsigned const which, size_t const index)
    {
        return static_cast<off_t>(
            base_offset + which * half_capacity +
            offsetof(MONAD_MPT_NAMESPACE::detail::db_metadata, device_sizes) +
            index * sizeof(uint64_t));
    }

    struct cnv0_geometry
    {
        file_offset_t base_offset;
        file_offset_t half_capacity;
    };

    cnv0_geometry geometry_of(storage_pool &pool)
    {
        auto &cnv = pool.chunk(storage_pool::cnv, 0);
        auto const fdr = cnv.read_fd();
        auto const fdw = cnv.write_fd(0);
        MONAD_ASSERT(fdr.second == fdw.second);
        return {fdr.second, cnv.capacity() / 2};
    }
}

TEST(device_resize, records_device_sizes_on_writable_open)
{
    auto const dev0 = create_temp_file(20 * BLKSIZE);
    auto const dev1 = create_temp_file(10 * BLKSIZE);
    auto const undevs = monad::make_scope_exit([&]() noexcept {
        std::filesystem::remove(dev0);
        std::filesystem::remove(dev1);
    });
    std::filesystem::path const both[] = {dev0, dev1};

    opened_db db{both, storage_pool::mode::create_if_needed};
    auto const devices = db.pool.devices();
    ASSERT_EQ(devices.size(), 2u);
    EXPECT_NE(devices[0].size_bytes(), devices[1].size_bytes())
        << "the two devices must differ in size, or a transposed recording "
           "would pass";

    for (unsigned which = 0; which < 2; which++) {
        auto const *const m = db.aux.metadata_ctx().main(which);
        EXPECT_EQ(m->device_sizes[0], devices[0].size_bytes())
            << "copy " << which;
        EXPECT_EQ(m->device_sizes[1], devices[1].size_bytes())
            << "copy " << which;
        // Slots past the device list stay at the not-recorded sentinel.
        for (size_t n = devices.size();
             n < MONAD_MPT_NAMESPACE::detail::db_metadata::MAX_RECORDED_DEVICES;
             n++) {
            EXPECT_EQ(m->device_sizes[n], 0u)
                << "copy " << which << " slot " << n;
        }
    }
}

// The recorded size is what a grow reads back, so an open which is not
// allowed to mutate the database must not touch it, and the next writable
// open must repair whatever it finds.
TEST(device_resize, read_only_open_leaves_recorded_device_sizes_alone)
{
    auto const dev0 = create_temp_file(20 * BLKSIZE);
    auto const undevs = monad::make_scope_exit(
        [&]() noexcept { std::filesystem::remove(dev0); });
    std::filesystem::path const one[] = {dev0};

    file_offset_t real_size = 0;
    file_offset_t base_offset = 0;
    file_offset_t half_capacity = 0;
    {
        opened_db db{one, storage_pool::mode::create_if_needed};
        real_size = db.pool.devices()[0].size_bytes();
        auto const g = geometry_of(db.pool);
        base_offset = g.base_offset;
        half_capacity = g.half_capacity;
    }
    ASSERT_GT(real_size, 0u);

    // Poison both copies behind the pool's back, leaving the dirty flag
    // clear so the next open is a plain one.
    constexpr uint64_t poison = 0xdeadbeefdeadbeefULL;
    {
        storage_pool pool{one, storage_pool::mode::open_existing};
        auto const fdw = pool.chunk(storage_pool::cnv, 0).write_fd(0);
        for (unsigned which = 0; which < 2; which++) {
            ASSERT_EQ(
                ssize_t(sizeof(poison)),
                ::pwrite(
                    fdw.first,
                    &poison,
                    sizeof(poison),
                    device_size_offset(base_offset, half_capacity, which, 0)));
        }
        ASSERT_EQ(0, ::fsync(fdw.first));
    }

    {
        storage_pool::creation_flags flags;
        flags.open_read_only = true;
        opened_db db{one, storage_pool::mode::open_existing, flags};
        for (unsigned which = 0; which < 2; which++) {
            EXPECT_EQ(
                db.aux.metadata_ctx().main(which)->device_sizes[0], poison)
                << "a read-only open rewrote the recorded size on copy "
                << which;
        }
    }

    opened_db db{one, storage_pool::mode::open_existing};
    for (unsigned which = 0; which < 2; which++) {
        EXPECT_EQ(db.aux.metadata_ctx().main(which)->device_sizes[0], real_size)
            << "copy " << which;
    }
}

namespace
{
    // Extends a pool device in place, exactly as lvextend would.
    void
    extend_in_place(std::filesystem::path const &path, file_offset_t const size)
    {
        int const fd = ::open(path.c_str(), O_RDWR);
        ASSERT_NE(fd, -1);
        auto const unfd =
            monad::make_scope_exit([fd]() noexcept { ::close(fd); });
        ASSERT_NE(-1, ::ftruncate(fd, static_cast<off_t>(size)));
    }
}

// The whole operation, storage layer through metadata layer: the pool sees
// more sequential chunks than chunk_info[] describes, and grows it onto the
// free list under the same intent record a device add uses.
TEST(device_resize, growing_a_device_grows_chunk_info_and_free_list)
{
    auto const dev0 = create_temp_file(20 * BLKSIZE);
    auto const undevs = monad::make_scope_exit(
        [&]() noexcept { std::filesystem::remove(dev0); });
    std::filesystem::path const one[] = {dev0};

    uint32_t before_count = 0;
    uint64_t before_capacity = 0;
    std::vector<uint32_t> before_free;
    file_offset_t recorded_size = 0;
    {
        opened_db db{one, storage_pool::mode::create_if_needed};
        auto const *m = db.aux.metadata_ctx().main();
        before_count = static_cast<uint32_t>(m->chunk_info_count);
        before_capacity = m->capacity_in_free_list;
        before_free = add_devices_test::free_list_ids(m);
        recorded_size = m->device_sizes[0];
    }
    ASSERT_GT(before_count, 0u);
    ASSERT_GT(recorded_size, 0u);

    extend_in_place(dev0, 26 * BLKSIZE + 16384);

    // What monad-mpt reads out of db_metadata and hands to the pool; the
    // storage layer has no way to consult the database itself.
    storage_pool::creation_flags flags;
    flags.recorded_size_of_grown_device = recorded_size;
    opened_db db{one, storage_pool::mode::add_devices, flags};
    auto const *m0 = db.aux.metadata_ctx().main(0);
    auto const *m1 = db.aux.metadata_ctx().main(1);
    auto const after_count = static_cast<uint32_t>(m0->chunk_info_count);
    EXPECT_EQ(after_count, db.io.chunk_count());
    EXPECT_GT(after_count, before_count);
    EXPECT_EQ(uint32_t(m1->chunk_info_count), after_count);

    // The old free-list order is preserved and the chunks the extend
    // uncovered follow it, in ascending order, at the tail.
    auto const after_free = add_devices_test::free_list_ids(m0);
    ASSERT_EQ(
        after_free.size(), before_free.size() + (after_count - before_count));
    for (size_t n = 0; n < before_free.size(); n++) {
        EXPECT_EQ(after_free[n], before_free[n]) << "free slot " << n;
    }
    for (uint32_t n = before_count; n < after_count; n++) {
        EXPECT_EQ(after_free[before_free.size() + (n - before_count)], n);
    }

    uint64_t added = 0;
    for (uint32_t n = before_count; n < after_count; n++) {
        added += db.pool.chunk(storage_pool::seq, n).capacity();
    }
    EXPECT_EQ(m0->capacity_in_free_list, before_capacity + added);
    EXPECT_EQ(
        m0->pending_shrink_grow.op_kind,
        MONAD_MPT_NAMESPACE::detail::db_metadata::PENDING_OP_NONE);

    // The grow recorded the device's new size, so a second extend has a
    // previous size to be taken up from.
    EXPECT_EQ(m0->device_sizes[0], db.pool.devices()[0].size_bytes());
    EXPECT_EQ(m1->device_sizes[0], db.pool.devices()[0].size_bytes());
}
