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
#include <filesystem>
#include <optional>
#include <span>
#include <vector>

MONAD_ASYNC_NAMESPACE_BEGIN

namespace test
{
    // The device_info_ fields compute_config_hash_ reads. A standalone
    // type rather than storage_pool::device_info_ itself, so this header
    // does not also need friend access to device_t::type_t_.
    struct StoragePoolConfigHashInput
    {
        uint64_t unique_hash;
        size_t chunks;
        uint32_t chunk_capacity;
    };

    // The device_info_ fields validate_devices_to_add_ reads. Lets a unit
    // test reach refusals whose real trigger is a device set far larger than
    // any test machine can provision.
    struct StoragePoolAddDevicesInput
    {
        bool has_pool_metadata;
        MONAD_ASYNC_NAMESPACE::file_offset_t size;
        uint32_t chunk_capacity;
        uint32_t num_cnv_chunks;
        uint32_t config_hash;
        size_t chunks;
    };

    // Test-only access to storage_pool's private on-disk hash formula, so a
    // unit test can pin a golden value against the real implementation
    // without a live device_t.
    struct StoragePoolTestAccess
    {
        static size_t validate_devices_to_add(
            std::span<std::filesystem::path const> const sources,
            std::span<StoragePoolAddDevicesInput const> const devices,
            std::optional<storage_pool::db_metadata_budget> const &budget =
                std::nullopt)
        {
            std::vector<storage_pool::device_info_> infos;
            infos.reserve(devices.size());
            for (size_t n = 0; n < devices.size(); n++) {
                storage_pool::device_info_ info{};
                info.size = devices[n].size;
                if (devices[n].has_pool_metadata) {
                    info.pool_metadata = storage_pool::device_pool_metadata_{
                        .chunk_capacity = devices[n].chunk_capacity,
                        .num_cnv_chunks = devices[n].num_cnv_chunks,
                        .config_hash = devices[n].config_hash,
                        .chunks = devices[n].chunks};
                }
                // Present so that a caller reaching the grown-device path,
                // which recomputes a hash from it, does not fault on an
                // absent identity. Duplicate sources are refused before
                // validate_devices_to_add_ is ever called.
                info.identity = storage_pool::device_identity_{
                    .dev = 0, .ino = n + 1, .rdev = 0, .hash_dev_no = 0};
                infos.push_back(info);
            }
            return storage_pool::validate_devices_to_add_(
                       sources, infos, std::nullopt, budget)
                .members;
        }

        static uint32_t compute_config_hash(
            std::span<StoragePoolConfigHashInput const> const devices)
        {
            std::vector<storage_pool::device_info_> infos;
            infos.reserve(devices.size());
            for (auto const &d : devices) {
                storage_pool::device_info_ info{};
                info.unique_hash = d.unique_hash;
                info.pool_metadata = storage_pool::device_pool_metadata_{
                    .chunk_capacity = d.chunk_capacity,
                    .num_cnv_chunks = 0,
                    .config_hash = 0,
                    .chunks = d.chunks};
                infos.push_back(info);
            }
            return storage_pool::compute_config_hash_(infos);
        }
    };
}

MONAD_ASYNC_NAMESPACE_END
