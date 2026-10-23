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

#include <category/async/config.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/assert.h>
#include <category/core/detail/start_lifetime_as_polyfill.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/detail/db_metadata.hpp>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <vector>

#include <sys/types.h>
#include <unistd.h>

MONAD_MPT_NAMESPACE_BEGIN

namespace test
{
    // The inverse of detail::migrate_monad008_to_monad009: narrows `copy`'s
    // records to MONAD008's 8-byte entries and stamps PREVIOUS_MAGIC. Every
    // count must fit MONAD008's 20 bits.
    inline void
    provision_monad008_metadata(detail::db_metadata *const copy) noexcept
    {
        using record_t = detail::db_metadata::chunk_record_t;
        using entry_t = detail::db_metadata::chunk_info_t;
        auto const n = static_cast<size_t>(copy->chunk_info_count);
        auto *const bytes = reinterpret_cast<std::byte *>(copy->chunk_records);
        for (size_t j = 0; j < n; ++j) {
            record_t record;
            std::memcpy(
                &record, bytes + j * sizeof(record_t), sizeof(record_t));
            MONAD_ASSERT(record.identity.count < (uint64_t{1} << 20));
            record.info.set_low_insertion_count_bits(record.identity.count);
            std::memcpy(
                bytes + j * sizeof(entry_t), &record.info, sizeof(entry_t));
        }
        // A MONAD008 pool upgraded from MONAD007 left stale bytes past its
        // entries, so nothing may rely on them reading as zero.
        std::memset(
            bytes + n * sizeof(entry_t),
            0xa5,
            n * (sizeof(record_t) - sizeof(entry_t)));
        std::memcpy(
            copy->magic,
            detail::db_metadata::PREVIOUS_MAGIC,
            detail::db_metadata::MAGIC_STRING_LEN);
    }

    // Calls `edit(copy, which)` on each metadata copy of `pool`, read from and
    // written back to cnv chunk 0 behind the pool's back. The span covers
    // MONAD009's records, which also covers MONAD008's entries. No
    // DbMetadataContext may have the pool open.
    template <class Edit>
    void
    edit_metadata_copies(MONAD_ASYNC_NAMESPACE::storage_pool &pool, Edit &&edit)
    {
        using detail::db_metadata;
        auto cnv = pool.chunk(MONAD_ASYNC_NAMESPACE::storage_pool::cnv, 0);
        auto const [fd, base] = cnv.write_fd(0);
        auto const half = cnv.capacity() / 2;
        for (unsigned which = 0; which < 2; ++which) {
            auto const at = static_cast<off_t>(base + which * half);
            std::vector<uint64_t> buffer(
                sizeof(db_metadata) / sizeof(uint64_t));
            MONAD_ASSERT(
                ::pread(fd, buffer.data(), sizeof(db_metadata), at) ==
                ssize_t(sizeof(db_metadata)));
            size_t const bytes =
                sizeof(db_metadata) +
                size_t(start_lifetime_as<db_metadata>(buffer.data())
                           ->chunk_info_count) *
                    sizeof(db_metadata::chunk_record_t);
            MONAD_ASSERT(bytes <= half);
            buffer.resize(bytes / sizeof(uint64_t));
            MONAD_ASSERT(
                ::pread(fd, buffer.data(), bytes, at) == ssize_t(bytes));
            edit(start_lifetime_as<db_metadata>(buffer.data()), which);
            MONAD_ASSERT(
                ::pwrite(fd, buffer.data(), bytes, at) == ssize_t(bytes));
        }
        MONAD_ASSERT(::fsync(fd) == 0);
    }

    inline void
    provision_monad008_pool(MONAD_ASYNC_NAMESPACE::storage_pool &pool)
    {
        edit_metadata_copies(
            pool, [](detail::db_metadata *const copy, unsigned) {
                provision_monad008_metadata(copy);
            });
    }
}

MONAD_MPT_NAMESPACE_END
