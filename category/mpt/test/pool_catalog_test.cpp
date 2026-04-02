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

#include <category/async/io.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/trie.hpp>

#include <gtest/gtest.h>

#include <cstdlib>
#include <filesystem>
#include <unistd.h>

using namespace monad::mpt;
using db_slot = MONAD_ASYNC_NAMESPACE::storage_pool::db_slot;

namespace
{
    struct TempFile
    {
        std::filesystem::path path;

        TempFile()
        {
            char tmpl[] = "pool_catalog_test_XXXXXX";
            int const fd = mkstemp(tmpl);
            MONAD_ASSERT(fd >= 0);
            ::close(fd);
            path = tmpl;
        }

        ~TempFile()
        {
            std::filesystem::remove(path);
        }
    };

    constexpr size_t CHUNK_CAPACITY = 1ul << 28;

    void truncate_file(std::filesystem::path const &p, size_t cnv, size_t seq)
    {
        auto const total = (cnv + seq) * CHUNK_CAPACITY + 24576;
        MONAD_ASSERT(-1 != ::truncate(p.c_str(), static_cast<off_t>(total)));
    }

    void init_db(MONAD_ASYNC_NAMESPACE::storage_pool &pool, uint16_t db_id = 1)
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
        UpdateAux aux{io, db_id};
        MONAD_ASSERT(aux.db_metadata() != nullptr);
    }
} // namespace

// Pool catalog: register, find, init DB2 on a fresh pool
TEST(pool_catalog, db2_register_and_init)
{
    TempFile f;
    truncate_file(f.path, 6, 20);
    MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
    flags.num_cnv_chunks = 6;
    MONAD_ASYNC_NAMESPACE::storage_pool pool{
        {&f.path, 1},
        MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate,
        flags};

    pool.register_db_slot(db_slot{
        .db_id = 2,
        .metadata_cnv_chunk_id = 3,
        .root_offset_cnv_start = 4,
        .root_offset_cnv_count = 2});

    auto const *slot = pool.find_db_slot(2);
    ASSERT_NE(slot, nullptr);
    EXPECT_EQ(slot->metadata_cnv_chunk_id, 3);
    EXPECT_EQ(slot->root_offset_cnv_start, 4);
    EXPECT_EQ(slot->root_offset_cnv_count, 2);
    EXPECT_EQ(pool.find_db_slot(99), nullptr);

    init_db(pool, 2);
}

// DB2 init on a live pool fails until Phase 1 shared freelist
TEST(pool_catalog, db2_live_pool_init_blocked)
{
    TempFile f;
    truncate_file(f.path, 6, 10);
    MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
    flags.num_cnv_chunks = 6;
    MONAD_ASYNC_NAMESPACE::storage_pool pool{
        {&f.path, 1},
        MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate,
        flags};

    pool.register_db_slot(db_slot{
        .db_id = 1,
        .metadata_cnv_chunk_id = 0,
        .root_offset_cnv_start = 1,
        .root_offset_cnv_count = 2});
    pool.register_db_slot(db_slot{
        .db_id = 2,
        .metadata_cnv_chunk_id = 3,
        .root_offset_cnv_start = 4,
        .root_offset_cnv_count = 2});

    init_db(pool, 1);
    // Make a seq chunk non-empty
    {
        auto &seq0 = pool.chunk(MONAD_ASYNC_NAMESPACE::storage_pool::seq, 0);
        auto [wfd, off] = seq0.write_fd(1);
        char byte = 'X';
        MONAD_ASSERT(::pwrite(wfd, &byte, 1, static_cast<off_t>(off)) == 1);
    }
    EXPECT_DEATH(init_db(pool, 2), "Phase 1");
}

// Legacy DB1 on interleaved 2-device pool resolves correctly
TEST(pool_catalog, interleaved_cnv_legacy_init)
{
    TempFile f1, f2;
    truncate_file(f1.path, 3, 10);
    truncate_file(f2.path, 3, 10);

    MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
    flags.num_cnv_chunks = 3;
    flags.interleave_chunks_evenly = true;
    std::filesystem::path paths[] = {f1.path, f2.path};
    MONAD_ASYNC_NAMESPACE::storage_pool pool{
        paths, MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate, flags};

    init_db(pool);
}

// End-to-end DB2 through AsyncIOContext
TEST(pool_catalog, db2_end_to_end_through_config)
{
    TempFile f;
    truncate_file(f.path, 6, 20);
    {
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
        flags.num_cnv_chunks = 6;
        MONAD_ASYNC_NAMESPACE::storage_pool pool{
            {&f.path, 1},
            MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate,
            flags};
        pool.register_db_slot(db_slot{
            .db_id = 2,
            .metadata_cnv_chunk_id = 3,
            .root_offset_cnv_start = 4,
            .root_offset_cnv_count = 2});
    }

    // RW init
    {
        OnDiskDbConfig c{};
        c.dbname_paths = {f.path};
        c.append = true;
        c.db_id = 2;
        AsyncIOContext ctx{c};
        UpdateAux aux{ctx.io, ctx.db_id};
        EXPECT_NE(aux.db_metadata(), nullptr);
    }
    // RO reopen
    {
        ReadOnlyOnDiskDbConfig c{};
        c.dbname_paths = {f.path};
        c.db_id = 2;
        AsyncIOContext ctx{c};
        UpdateAux aux{ctx.io, ctx.db_id};
        EXPECT_NE(aux.db_metadata(), nullptr);
    }
}

// --- Catalog validation ---

TEST(pool_catalog, rejects_out_of_range_metadata_cnv)
{
    TempFile f;
    truncate_file(f.path, 3, 10);
    MONAD_ASYNC_NAMESPACE::storage_pool pool{
        {&f.path, 1}, MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate, {}};
    EXPECT_DEATH(
        pool.register_db_slot(db_slot{
            .db_id = 2,
            .metadata_cnv_chunk_id = 5,
            .root_offset_cnv_start = 1,
            .root_offset_cnv_count = 1}),
        "out of range");
}

TEST(pool_catalog, rejects_out_of_range_root_offset)
{
    TempFile f;
    truncate_file(f.path, 3, 10);
    MONAD_ASYNC_NAMESPACE::storage_pool pool{
        {&f.path, 1}, MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate, {}};
    EXPECT_DEATH(
        pool.register_db_slot(db_slot{
            .db_id = 2,
            .metadata_cnv_chunk_id = 0,
            .root_offset_cnv_start = 2,
            .root_offset_cnv_count = 2}),
        "out of range");
}

TEST(pool_catalog, rejects_metadata_overlapping_root_offsets)
{
    TempFile f;
    truncate_file(f.path, 4, 10);
    MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
    flags.num_cnv_chunks = 4;
    MONAD_ASYNC_NAMESPACE::storage_pool pool{
        {&f.path, 1},
        MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate,
        flags};
    EXPECT_DEATH(
        pool.register_db_slot(db_slot{
            .db_id = 2,
            .metadata_cnv_chunk_id = 1,
            .root_offset_cnv_start = 1,
            .root_offset_cnv_count = 2}),
        "overlaps root_offset");
}

TEST(pool_catalog, rejects_duplicate_db_id)
{
    TempFile f;
    truncate_file(f.path, 6, 10);
    MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
    flags.num_cnv_chunks = 6;
    MONAD_ASYNC_NAMESPACE::storage_pool pool{
        {&f.path, 1},
        MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate,
        flags};
    pool.register_db_slot(db_slot{
        .db_id = 2,
        .metadata_cnv_chunk_id = 3,
        .root_offset_cnv_start = 4,
        .root_offset_cnv_count = 2});
    EXPECT_DEATH(
        pool.register_db_slot(db_slot{
            .db_id = 2,
            .metadata_cnv_chunk_id = 0,
            .root_offset_cnv_start = 1,
            .root_offset_cnv_count = 2}),
        "Duplicate db_id");
}

TEST(pool_catalog, rejects_overlapping_slots)
{
    TempFile f;
    truncate_file(f.path, 6, 10);
    MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
    flags.num_cnv_chunks = 6;
    MONAD_ASYNC_NAMESPACE::storage_pool pool{
        {&f.path, 1},
        MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate,
        flags};
    pool.register_db_slot(db_slot{
        .db_id = 1,
        .metadata_cnv_chunk_id = 0,
        .root_offset_cnv_start = 1,
        .root_offset_cnv_count = 2});
    EXPECT_DEATH(
        pool.register_db_slot(db_slot{
            .db_id = 3,
            .metadata_cnv_chunk_id = 4,
            .root_offset_cnv_start = 2,
            .root_offset_cnv_count = 2}),
        "overlaps with existing");
}
