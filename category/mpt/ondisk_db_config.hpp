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

#include <filesystem>
#include <optional>
#include <vector>

MONAD_MPT_NAMESPACE_BEGIN

struct StateMachine;

struct OnDiskDbConfig
{
    bool append{false};
    bool compaction{false};
    bool capture_io_latencies{false};
    bool eager_completions{false};
    bool rewind_to_latest_finalized{false};
    unsigned rd_buffers{1024};
    unsigned wr_buffers{4};
    unsigned uring_entries{512};
    std::optional<unsigned> sq_thread_cpu{0};
    std::optional<uint64_t> start_block_id{std::nullopt};
    std::vector<std::filesystem::path> dbname_paths{};
    int64_t file_size_db{512}; // truncate files to this size
    unsigned concurrent_read_io_limit{1024};
    // fixed history length if contains value, otherwise rely on db to adjust
    // history length upon disk usage
    std::optional<uint64_t> fixed_history_length{std::nullopt};
    // Number of chunks to allocate for root offsets when initializing the disk.
    // Each chunk can hold 1 << 24 = 16777216 historical entries.
    // This field must be power of 2.
    uint32_t root_offsets_chunk_count{2};
    // Maximum memory for NodeCache LRU cache
    uint64_t node_lru_max_mem{1ul << 30}; // 1GB
};

struct ReadOnlyOnDiskDbConfig
{
    bool disable_mismatching_storage_pool_check{
        false}; // risk of severe data loss
    bool capture_io_latencies{false};
    bool eager_completions{false};
    unsigned rd_buffers{1024};
    unsigned uring_entries{128};
    // default to disable sqpoll kernel thread since now ReadOnlyDb uses
    // blocking read
    std::optional<unsigned> sq_thread_cpu{std::nullopt};
    std::vector<std::filesystem::path> dbname_paths;
    unsigned concurrent_read_io_limit{600};
    uint64_t node_lru_max_mem{100ul << 20}; // 100MB
};

MONAD_MPT_NAMESPACE_END
