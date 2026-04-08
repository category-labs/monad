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
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/trie.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <fcntl.h>
#include <filesystem>
#include <stdlib.h>
#include <unistd.h>
#include <vector>

using namespace monad::mpt;
using db_slot = MONAD_ASYNC_NAMESPACE::storage_pool::db_slot;

namespace
{
    constexpr size_t CHUNK_CAPACITY = 1ul << 28;

    std::filesystem::path make_pool_file(size_t cnv, size_t seq)
    {
        auto path = MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
                    "pool_catalog_test_XXXXXX";
        int const fd = ::mkstemp((char *)path.native().data());
        MONAD_ASSERT(fd >= 0);
        auto const bytes = (cnv + seq) * CHUNK_CAPACITY + 24576;
        MONAD_ASSERT(-1 != ::ftruncate(fd, static_cast<off_t>(bytes)));
        ::close(fd);
        return path;
    }

    void init_db(MONAD_ASYNC_NAMESPACE::storage_pool &pool, uint8_t db_id = 1)
    {
        monad::io::Ring rr{monad::io::RingConfig{2}};
        monad::io::Ring wr{monad::io::RingConfig{4}};
        auto rwbuf = monad::io::make_buffers_for_segregated_read_write(
            rr,
            wr,
            2,
            4,
            MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
            MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        MONAD_ASYNC_NAMESPACE::AsyncIO io{pool, rwbuf};
        UpdateAux const aux{io, db_id};
        MONAD_ASSERT(aux.db_metadata() != nullptr);
    }
} // namespace

TEST(pool_catalog, db2_register_and_init)
{
    auto const f = make_pool_file(6, 20);
    auto const cleanup_f =
        monad::make_scope_exit([&]() noexcept { std::filesystem::remove(f); });
    MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
    flags.num_cnv_chunks = 6;
    MONAD_ASYNC_NAMESPACE::storage_pool pool{
        {&f, 1}, MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate, flags};

    pool.register_db_slot(db_slot{
        .db_id = 2,
        .metadata_cnv = 3,
        .root_offset_cnv_start = 4,
        .root_offset_cnv_count = 2});

    auto const *slot = pool.find_db_slot(2);
    ASSERT_NE(slot, nullptr);
    EXPECT_EQ(slot->metadata_cnv, 3);
    EXPECT_EQ(slot->root_offset_cnv_start, 4);
    EXPECT_EQ(slot->root_offset_cnv_count, 2);
    for (uint8_t id = 3; id <= 99; ++id) {
        EXPECT_EQ(pool.find_db_slot(id), nullptr);
    }
}

// DB2 can reopen as read-only through AsyncIOContext
TEST(pool_catalog, db2_can_reopen_as_ro)
{
    auto const f = make_pool_file(6, 20);
    auto const cleanup_f =
        monad::make_scope_exit([&]() noexcept { std::filesystem::remove(f); });
    {
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
        flags.num_cnv_chunks = 6;
        MONAD_ASYNC_NAMESPACE::storage_pool pool{
            {&f, 1},
            MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate,
            flags};
        pool.register_db_slot(db_slot{
            .db_id = 2,
            .metadata_cnv = 3,
            .root_offset_cnv_start = 4,
            .root_offset_cnv_count = 2});
    }

    // RW init
    {
        OnDiskDbConfig c{};
        c.dbname_paths = {f};
        c.append = true;
        c.db_id = 2;
        AsyncIOContext ctx{c};
        UpdateAux const aux{ctx.io, ctx.db_id};
        EXPECT_NE(aux.db_metadata(), nullptr);
    }
    // RO reopen
    {
        ReadOnlyOnDiskDbConfig c{};
        c.dbname_paths = {f};
        c.db_id = 2;
        AsyncIOContext ctx{c};
        UpdateAux const aux{ctx.io, ctx.db_id};
        EXPECT_NE(aux.db_metadata(), nullptr);
    }
}

TEST(pool_catalog, out_of_range_metadata)
{
    constexpr size_t pool_cnv = 3;
    constexpr size_t pool_seq = 10;
    auto const f = make_pool_file(pool_cnv, pool_seq);
    auto const cleanup_f =
        monad::make_scope_exit([&]() noexcept { std::filesystem::remove(f); });
    MONAD_ASYNC_NAMESPACE::storage_pool pool{
        {&f, 1}, MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate, {}};
    EXPECT_DEATH(
        pool.register_db_slot(db_slot{
            .db_id = 2,
            .metadata_cnv = 5, // exceeds pool_cnv
            .root_offset_cnv_start = 1,
            .root_offset_cnv_count = 1}),
        "out of range");
    EXPECT_DEATH(
        pool.register_db_slot(db_slot{
            .db_id = 2,
            .metadata_cnv = 0,
            .root_offset_cnv_start = 2,
            .root_offset_cnv_count = 2}), // range [2,4) exceeds pool_cnv
        "out of range");
    // metadata=1, root_offsets=[1,3) — metadata sits inside its own
    // root offset range
    EXPECT_DEATH(
        pool.register_db_slot(db_slot{
            .db_id = 2,
            .metadata_cnv = 1,
            .root_offset_cnv_start = 1,
            .root_offset_cnv_count = 2}),
        "overlaps root_offset");
}

TEST(pool_catalog, rejects_duplicate_db_id)
{
    constexpr size_t pool_cnv = 6;
    constexpr size_t pool_seq = 10;
    auto const f = make_pool_file(pool_cnv, pool_seq);
    auto const cleanup_f =
        monad::make_scope_exit([&]() noexcept { std::filesystem::remove(f); });
    MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
    flags.num_cnv_chunks = pool_cnv;
    MONAD_ASYNC_NAMESPACE::storage_pool pool{
        {&f, 1}, MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate, flags};
    pool.register_db_slot(db_slot{
        .db_id = 2,
        .metadata_cnv = 3,
        .root_offset_cnv_start = 4,
        .root_offset_cnv_count = 2});
    EXPECT_DEATH(
        pool.register_db_slot(db_slot{
            .db_id = 2, // duplicate
            .metadata_cnv = 0,
            .root_offset_cnv_start = 1,
            .root_offset_cnv_count = 2}),
        "Duplicate db_id");
}

TEST(pool_catalog, rejects_overlapping_slots)
{
    constexpr size_t pool_cnv = 6;
    constexpr size_t pool_seq = 10;
    auto const f = make_pool_file(pool_cnv, pool_seq);
    auto const cleanup_f =
        monad::make_scope_exit([&]() noexcept { std::filesystem::remove(f); });
    MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
    flags.num_cnv_chunks = pool_cnv;
    MONAD_ASYNC_NAMESPACE::storage_pool pool{
        {&f, 1}, MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate, flags};
    pool.register_db_slot(db_slot{
        .db_id = 1,
        .metadata_cnv = 0,
        .root_offset_cnv_start = 1,
        .root_offset_cnv_count = 2}); // DB1 occupies cnv [0, 1, 2]
    EXPECT_DEATH(
        pool.register_db_slot(db_slot{
            .db_id = 3,
            .metadata_cnv = 4,
            .root_offset_cnv_start = 2, // cnv 2 overlaps DB1's root offsets
            .root_offset_cnv_count = 2}),
        "overlaps with existing");
}

// --- Regression tests ---

// Pre-MND1 pool rejected on create_if_needed instead of silently reinitializing
TEST(pool_catalog, rejects_old_format_on_create_if_needed)
{
    auto const f = make_pool_file(3, 10);
    auto const cleanup_f =
        monad::make_scope_exit([&]() noexcept { std::filesystem::remove(f); });
    // Mock an old MND0 pool
    {
        MONAD_ASYNC_NAMESPACE::storage_pool const pool{
            {&f, 1}, MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate, {}};
    }
    {
        int const fd = ::open(f.c_str(), O_RDWR);
        MONAD_ASSERT(fd != -1);
        struct stat st;
        ::fstat(fd, &st);
        // Magic is the last 4 bytes of the file
        char old_magic[] = "MND0";
        MONAD_ASSERT(::pwrite(fd, old_magic, 4, st.st_size - 4) == 4);
        ::close(fd);
    }
    EXPECT_DEATH(
        ({
            MONAD_ASYNC_NAMESPACE::storage_pool const pool(
                std::span{&f, 1},
                MONAD_ASYNC_NAMESPACE::storage_pool::mode::create_if_needed,
                {});
        }),
        "incompatible format");
}

// Existing pool with DB1 can add DB2 without restating DB1's geometry
TEST(pool_catalog, add_db2_to_existing_pool)
{
    auto const f = make_pool_file(6, 20);
    auto const cleanup_f =
        monad::make_scope_exit([&]() noexcept { std::filesystem::remove(f); });
    // Create pool with DB1 only
    {
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
        flags.num_cnv_chunks = 6;
        MONAD_ASYNC_NAMESPACE::storage_pool pool{
            {&f, 1},
            MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate,
            flags};
        pool.register_db_slot(db_slot{
            .db_id = 1,
            .metadata_cnv = 0,
            .root_offset_cnv_start = 1,
            .root_offset_cnv_count = 2});
        init_db(pool, 1);
    }
    // Reopen and add DB2
    {
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
        flags.num_cnv_chunks = 6;
        MONAD_ASYNC_NAMESPACE::storage_pool pool{
            {&f, 1},
            MONAD_ASYNC_NAMESPACE::storage_pool::mode::open_existing,
            flags};
        ASSERT_NE(pool.find_db_slot(1), nullptr);
        ASSERT_EQ(pool.find_db_slot(2), nullptr);
        pool.register_db_slot(db_slot{
            .db_id = 2,
            .metadata_cnv = 3,
            .root_offset_cnv_start = 4,
            .root_offset_cnv_count = 2});
        ASSERT_NE(pool.find_db_slot(2), nullptr);
        init_db(pool, 2);
    }
    // Verify both survive reopen
    {
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
        flags.num_cnv_chunks = 6;
        MONAD_ASYNC_NAMESPACE::storage_pool const pool{
            {&f, 1},
            MONAD_ASYNC_NAMESPACE::storage_pool::mode::open_existing,
            flags};
        EXPECT_NE(pool.find_db_slot(1), nullptr);
        EXPECT_NE(pool.find_db_slot(2), nullptr);
    }
}

// Migration simulation: DB1 shrinks, DB2 grows into the freed capacity
TEST(pool_catalog, migration_simulation)
{
    constexpr size_t pool_cnv = 6;
    constexpr size_t pool_seq = 20;
    auto const f = make_pool_file(pool_cnv, pool_seq);
    auto const cleanup_f =
        monad::make_scope_exit([&]() noexcept { std::filesystem::remove(f); });
    MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
    flags.num_cnv_chunks = pool_cnv;
    MONAD_ASYNC_NAMESPACE::storage_pool pool{
        {&f, 1}, MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate, flags};

    pool.register_db_slot(db_slot{
        .db_id = 1,
        .metadata_cnv = 0,
        .root_offset_cnv_start = 1,
        .root_offset_cnv_count = 2});
    pool.register_db_slot(db_slot{
        .db_id = 2,
        .metadata_cnv = 3,
        .root_offset_cnv_start = 4,
        .root_offset_cnv_count = 2});

    auto const total_free = pool.free_seq_chunk_count();

    constexpr uint32_t db1_limit = 6;
    std::vector<uint32_t> db1_chunks;
    {
        monad::io::Ring rr{monad::io::RingConfig{2}};
        monad::io::Ring wr{monad::io::RingConfig{4}};
        auto rwbuf = monad::io::make_buffers_for_segregated_read_write(
            rr,
            wr,
            2,
            4,
            MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
            MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        MONAD_ASYNC_NAMESPACE::AsyncIO io{pool, rwbuf};
        UpdateAux aux{io, 1};
        aux.set_max_seq_chunks(db1_limit);
        auto const after_init =
            aux.num_chunks(UpdateAuxImpl::chunk_list::fast) +
            aux.num_chunks(UpdateAuxImpl::chunk_list::slow);
        ASSERT_EQ(after_init, 2u); // fast + slow
        for (uint32_t i = after_init; i < db1_limit; ++i) {
            auto const id = pool.allocate_seq_chunk(1);
            ASSERT_NE(id, MONAD_ASYNC_NAMESPACE::storage_pool::ALLOC_FAILED);
            aux.append(UpdateAuxImpl::chunk_list::fast, id);
            pool.commit_seq_chunk(id);
            db1_chunks.push_back(id);
        }
        auto const db1_owned = aux.num_chunks(UpdateAuxImpl::chunk_list::fast) +
                               aux.num_chunks(UpdateAuxImpl::chunk_list::slow);
        EXPECT_EQ(db1_owned, db1_limit);
        EXPECT_GE(aux.disk_usage(), 1.0);
    }
    EXPECT_EQ(pool.free_seq_chunk_count(), total_free - db1_limit);

    // DB1 "shrinks": return 4 chunks to pool (simulating compaction)
    for (auto const id : db1_chunks) {
        pool.begin_free_seq_chunk(id);
        pool.free_seq_chunk(id);
    }
    EXPECT_EQ(pool.free_seq_chunk_count(), total_free - 2); // fast+slow remain

    // DB2 grows into the capacity DB1 freed
    {
        monad::io::Ring rr{monad::io::RingConfig{2}};
        monad::io::Ring wr{monad::io::RingConfig{4}};
        auto rwbuf = monad::io::make_buffers_for_segregated_read_write(
            rr,
            wr,
            2,
            4,
            MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
            MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        MONAD_ASYNC_NAMESPACE::AsyncIO io{pool, rwbuf};
        UpdateAux aux{io, 2};
        auto const db2_after_init =
            aux.num_chunks(UpdateAuxImpl::chunk_list::fast) +
            aux.num_chunks(UpdateAuxImpl::chunk_list::slow);
        ASSERT_EQ(db2_after_init, 2u); // fast + slow

        constexpr uint32_t db2_limit = 6;
        aux.set_max_seq_chunks(db2_limit);

        for (uint32_t i = db2_after_init; i < db2_limit; ++i) {
            auto const id = pool.allocate_seq_chunk(2);
            ASSERT_NE(id, MONAD_ASYNC_NAMESPACE::storage_pool::ALLOC_FAILED);
            aux.append(UpdateAuxImpl::chunk_list::fast, id);
            pool.commit_seq_chunk(id);
        }

        auto const db2_owned = aux.num_chunks(UpdateAuxImpl::chunk_list::fast) +
                               aux.num_chunks(UpdateAuxImpl::chunk_list::slow);
        EXPECT_EQ(db2_owned, db2_limit);
        EXPECT_GE(aux.disk_usage(), 1.0);
    }
}

// Simulate crash during allocation: find_reserved_chunk finds orphaned chunks
TEST(pool_catalog, find_reserved_chunk_after_crash)
{
    auto const f = make_pool_file(3, 10);
    auto const cleanup_f =
        monad::make_scope_exit([&]() noexcept { std::filesystem::remove(f); });
    {
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
        flags.num_cnv_chunks = 3;
        MONAD_ASYNC_NAMESPACE::storage_pool pool{
            {&f, 1},
            MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate,
            flags};
        // Allocate but never commit — simulates crash mid-allocation.
        auto const id = pool.allocate_seq_chunk(1);
        ASSERT_NE(id, MONAD_ASYNC_NAMESPACE::storage_pool::ALLOC_FAILED);
    }
    // Reopen — find_reserved_chunk should locate the orphan.
    {
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
        flags.num_cnv_chunks = 3;
        MONAD_ASYNC_NAMESPACE::storage_pool pool{
            {&f, 1},
            MONAD_ASYNC_NAMESPACE::storage_pool::mode::open_existing,
            flags};
        auto const reserved = pool.find_reserved_chunk(1);
        ASSERT_NE(reserved, MONAD_ASYNC_NAMESPACE::storage_pool::ALLOC_FAILED);
        // Not in any DB list → reclaim.
        pool.free_seq_chunk(reserved);
        EXPECT_EQ(
            pool.find_reserved_chunk(1),
            MONAD_ASYNC_NAMESPACE::storage_pool::ALLOC_FAILED);
        auto const total_seq =
            pool.chunks(MONAD_ASYNC_NAMESPACE::storage_pool::seq);
        EXPECT_EQ(pool.free_seq_chunk_count(), total_seq);
    }
}

// Simulate crash during free: begin_free leaves chunk RESERVED
TEST(pool_catalog, find_reserved_chunk_after_crash_during_free)
{
    auto const f = make_pool_file(3, 10);
    auto const cleanup_f =
        monad::make_scope_exit([&]() noexcept { std::filesystem::remove(f); });
    {
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
        flags.num_cnv_chunks = 3;
        MONAD_ASYNC_NAMESPACE::storage_pool pool{
            {&f, 1},
            MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate,
            flags};
        auto const id = pool.allocate_seq_chunk(1);
        ASSERT_NE(id, MONAD_ASYNC_NAMESPACE::storage_pool::ALLOC_FAILED);
        pool.commit_seq_chunk(id);
        // Begin free but don't finish — simulates crash mid-free.
        pool.begin_free_seq_chunk(id);
    }
    // Reopen — find_reserved_chunk should locate it.
    {
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
        flags.num_cnv_chunks = 3;
        MONAD_ASYNC_NAMESPACE::storage_pool pool{
            {&f, 1},
            MONAD_ASYNC_NAMESPACE::storage_pool::mode::open_existing,
            flags};
        auto const reserved = pool.find_reserved_chunk(1);
        ASSERT_NE(reserved, MONAD_ASYNC_NAMESPACE::storage_pool::ALLOC_FAILED);
        // Caller would check DB list and decide. Here, just free it.
        pool.free_seq_chunk(reserved);
        auto const total_seq =
            pool.chunks(MONAD_ASYNC_NAMESPACE::storage_pool::seq);
        EXPECT_EQ(pool.free_seq_chunk_count(), total_seq);
    }
}

// Multiple RESERVED chunks (reentrancy crash) are all reconciled on reopen
TEST(pool_catalog, reconcile_multiple_reserved_chunks)
{
    auto const f = make_pool_file(3, 10);
    auto const cleanup_f =
        monad::make_scope_exit([&]() noexcept { std::filesystem::remove(f); });
    {
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
        flags.num_cnv_chunks = 3;
        MONAD_ASYNC_NAMESPACE::storage_pool pool{
            {&f, 1},
            MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate,
            flags};
        pool.register_db_slot(MONAD_ASYNC_NAMESPACE::storage_pool::db_slot{
            .db_id = 1,
            .metadata_cnv = 0,
            .root_offset_cnv_start = 1,
            .root_offset_cnv_count = 2});
        init_db(pool, 1);
        // Simulate reentrancy crash: two chunks allocated but never
        // committed — both left RESERVED.
        auto const id1 = pool.allocate_seq_chunk(1);
        auto const id2 = pool.allocate_seq_chunk(1);
        ASSERT_NE(id1, MONAD_ASYNC_NAMESPACE::storage_pool::ALLOC_FAILED);
        ASSERT_NE(id2, MONAD_ASYNC_NAMESPACE::storage_pool::ALLOC_FAILED);
    }
    // Reopen writable — set_io should reconcile both RESERVED chunks.
    {
        OnDiskDbConfig c{};
        c.dbname_paths = {f};
        c.append = true;
        c.db_id = 1;
        AsyncIOContext ctx{c};
        UpdateAux const aux{ctx.io, ctx.db_id};
        // Both orphaned chunks should have been freed.
        EXPECT_EQ(
            ctx.io.storage_pool().find_reserved_chunk(1),
            MONAD_ASYNC_NAMESPACE::storage_pool::ALLOC_FAILED);
    }
}
