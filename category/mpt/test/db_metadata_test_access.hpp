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

#pragma once

#include <category/mpt/config.hpp>
#include <category/mpt/detail/db_metadata.hpp>

#include <cstdint>

MONAD_MPT_NAMESPACE_BEGIN

namespace test
{
    // Test-only access to root_offsets_ring_t's private scalars/storage (made
    // private to force atomic access). Single-threaded / offline use only.
    struct DbMetadataTestAccess
    {
        using ring = detail::db_metadata::root_offsets_ring_t;

        static uint64_t version_lower_bound(ring const &r) noexcept
        {
            return r.version_lower_bound_;
        }

        static uint64_t next_version(ring const &r) noexcept
        {
            return r.next_version_;
        }

        static void set_version_lower_bound(ring &r, uint64_t const v) noexcept
        {
            r.version_lower_bound_ = v;
        }

        static void set_next_version(ring &r, uint64_t const v) noexcept
        {
            r.next_version_ = v;
        }

        static auto &storage(ring &r) noexcept
        {
            return r.storage_;
        }

        static auto const &storage(ring const &r) noexcept
        {
            return r.storage_;
        }
    };
}

MONAD_MPT_NAMESPACE_END
