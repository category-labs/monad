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

#include <cstddef>
#include <cstdint>
#include <optional>

MONAD_ASYNC_NAMESPACE_BEGIN

namespace test
{
    // The device_info_ fields validate_device_to_grow_ reads. Lets a unit
    // test reach refusals whose real trigger is a device far larger than any
    // test machine can provision.
    struct StoragePoolGrowInput
    {
        MONAD_ASYNC_NAMESPACE::file_offset_t size;
        uint32_t chunk_capacity;
        uint32_t num_cnv_chunks;
    };

    // Test-only access to storage_pool's private on-disk hash formula, so a
    // unit test can pin a golden value against the real implementation
    // without a live device_t.
    struct StoragePoolTestAccess
    {
        static void validate_device_to_grow(
            StoragePoolGrowInput const &device,
            std::optional<storage_pool::db_metadata_budget> const &budget)
        {
            storage_pool::device_info_ info{};
            info.size = device.size;
            info.pool_metadata = storage_pool::device_pool_metadata_{
                .chunk_capacity = device.chunk_capacity,
                .num_cnv_chunks = device.num_cnv_chunks,
                // Never adopted, so the footer's identity check passes over it
                // and the size refusals this reaches for are the ones that
                // fire. A synthetic device has no hash worth computing.
                .config_hash = 0,
                .chunks = 0};
            (void)storage_pool::validate_device_to_grow_(
                "device", info, std::nullopt, budget);
        }

        static uint32_t compute_config_hash(
            uint64_t const unique_hash, size_t const chunks,
            uint32_t const chunk_capacity)
        {
            return storage_pool::compute_config_hash_(
                unique_hash, chunks, chunk_capacity);
        }
    };
}

MONAD_ASYNC_NAMESPACE_END
