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

#pragma once

#include <category/async/io.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/assert.h>
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>
#include <category/core/test_util/temp_file_cleanup.hpp>
#include <category/mpt/db_metadata_context.hpp>
#include <category/mpt/detail/db_metadata.hpp>
#include <category/mpt/trie.hpp>

#include <cstdint>
#include <filesystem>
#include <span>
#include <vector>

#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>

namespace rescan_test
{
    // The fixtures size devices in whole chunks, so this is both the chunk
    // capacity and the unit they extend by. Kept small: pool creation
    // 0xff-fills the root-offsets ring, so the default 256 Mb capacity costs
    // half a gigabyte of real writes per test.
    inline constexpr uint32_t CHUNK_CAPACITY_BITS = 24;
    inline constexpr MONAD_ASYNC_NAMESPACE::file_offset_t BLKSIZE =
        1ULL << CHUNK_CAPACITY_BITS;

    inline MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags
    small_chunk_flags()
    {
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
        flags.set_chunk_capacity(CHUNK_CAPACITY_BITS);
        return flags;
    }

    inline std::filesystem::path
    create_temp_file(MONAD_ASYNC_NAMESPACE::file_offset_t const length)
    {
        monad::test::remove_stale_temp_files_once(
            MONAD_ASYNC_NAMESPACE::working_temporary_directory(),
            "monad_rescan_test_");
        std::filesystem::path ret(
            MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
            "monad_rescan_test_XXXXXX");
        int const fd = ::mkstemp((char *)ret.native().data());
        MONAD_ASSERT(fd != -1);
        MONAD_ASSERT(-1 != ::ftruncate(fd, static_cast<off_t>(length + 16384)));
        ::close(fd);
        return ret;
    }

    inline monad::io::Buffers make_buffers(
        bool const read_only, monad::io::Ring &rd_ring,
        monad::io::Ring &wr_ring)
    {
        constexpr size_t rd_size =
            MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE;
        constexpr size_t wr_size =
            MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE;
        if (read_only) {
            return monad::io::make_buffers_for_read_only(rd_ring, 2, rd_size);
        }
        return monad::io::make_buffers_for_segregated_read_write(
            rd_ring, wr_ring, 2, 4, rd_size, wr_size);
    }

    // Opens the pool through a full AsyncIO and UpdateAux so the metadata
    // constructor runs exactly as it does in production.
    struct opened_db
    {
        MONAD_ASYNC_NAMESPACE::storage_pool pool;
        monad::io::Ring rd_ring;
        monad::io::Ring wr_ring;
        monad::io::Buffers buffers;
        MONAD_ASYNC_NAMESPACE::AsyncIO io;
        MONAD_MPT_NAMESPACE::UpdateAux aux;

        opened_db(
            std::filesystem::path const &dev,
            MONAD_ASYNC_NAMESPACE::storage_pool::mode const mode,
            MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags const flags =
                small_chunk_flags())
            : pool{dev, mode, flags}
            , rd_ring{monad::io::RingConfig{2}}
            , wr_ring{monad::io::RingConfig{4}}
            , buffers{make_buffers(pool.is_read_only(), rd_ring, wr_ring)}
            , io{pool, buffers}
            , aux{io}
        {
        }
    };

    // Extends the device in place, exactly as lvextend would.
    inline void extend_in_place(
        std::filesystem::path const &path,
        MONAD_ASYNC_NAMESPACE::file_offset_t const size)
    {
        int const fd = ::open(path.c_str(), O_RDWR);
        MONAD_ASSERT(fd != -1);
        auto const unfd =
            monad::make_scope_exit([fd]() noexcept { ::close(fd); });
        MONAD_ASSERT(-1 != ::ftruncate(fd, static_cast<off_t>(size)));
    }

    // What monad-mpt hands the pool: the size db_metadata recorded for the
    // device, which is the only thing that can locate the stranded metadata.
    inline MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags
    rescan_flags(MONAD_ASYNC_NAMESPACE::file_offset_t const recorded)
    {
        auto flags = small_chunk_flags();
        flags.recorded_size_of_grown_device = recorded;
        flags.metadata_budget =
            MONAD_ASYNC_NAMESPACE::storage_pool::db_metadata_budget{
                .header_bytes = MONAD_MPT_NAMESPACE::detail::db_metadata::
                    MONAD007_HEADER_BYTES,
                .bytes_per_chunk = sizeof(
                    MONAD_MPT_NAMESPACE::detail::db_metadata::chunk_info_t)};
        return flags;
    }

    // The free list in list order.
    inline std::vector<uint32_t>
    free_list_ids(MONAD_MPT_NAMESPACE::detail::db_metadata const *const m)
    {
        std::vector<uint32_t> ret;
        for (auto const *i = m->free_list_begin(); i != nullptr;
             i = i->next(m)) {
            ret.push_back(i->index(m));
        }
        return ret;
    }
}
