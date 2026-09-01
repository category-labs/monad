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

#include <category/mpt/config.hpp>
#include <category/mpt/detail/collected_stats.hpp>

#include <atomic>
#include <cstdint>
#include <filesystem>
#include <optional>
#include <type_traits>

MONAD_MPT_NAMESPACE_BEGIN

namespace detail
{
    // Layout of the statistics sidecar: a small file the writing process maps
    // shared and writes, so a scraper in another process can read counters
    // that otherwise live only in this process's memory. Nothing in the db
    // depends on it; a db whose sidecar cannot be mapped runs without one.
    //
    // Exactly one process may publish to a path at a time. The seqlock assumes
    // it, and create() enforces it with an exclusive flock.
    //
    // Sections after the header are append-only, and appending does not bump
    // format_version: payload_size alone says which sections a writer wrote,
    // so a reader accepts a writer of any age and reports the sections it
    // predates as absent. A layout change that is not an append bumps
    // format_version, which readers require to match exactly.
    struct db_stats_shm
    {
        static constexpr uint64_t MAGIC = 0x4d4f4e4144535453; // "MONADSTS"
        static constexpr uint32_t FORMAT_VERSION = 1;
        static constexpr uint32_t HEADER_SIZE = 24;

        uint64_t magic;
        uint32_t format_version;
        uint32_t payload_size; // bytes of sections following this header
        uint32_t seq; // odd while a publish is in flight
        uint32_t unused_; // always zero

        TrieUpdateCollectedStats update_stats;
    };

    static_assert(std::is_trivially_copyable_v<db_stats_shm>);
    static_assert(
        sizeof(db_stats_shm) ==
        db_stats_shm::HEADER_SIZE + sizeof(TrieUpdateCollectedStats));
    // A reader maps this much even when the writer's file is shorter, which is
    // only safe while it all lands in the page that holds end of file.
    static_assert(sizeof(db_stats_shm) <= 4096);
    // A lock-based atomic_ref would take a lock table private to one process,
    // leaving the seqlock synchronizing nothing across the boundary it exists
    // to cross.
    static_assert(std::atomic_ref<uint32_t>::is_always_lock_free);
    static_assert(std::atomic_ref<uint64_t>::is_always_lock_free);
}

class DbStatsPublisher
{
    detail::db_stats_shm *shm_{nullptr};
    int fd_{-1}; // held open for the flock that keeps this writer exclusive

    DbStatsPublisher(detail::db_stats_shm *const shm, int const fd) noexcept
        : shm_{shm}
        , fd_{fd}
    {
    }

public:
    // Creates `path`, or takes over the sidecar already there, and maps it
    // shared. Returns nullopt after logging if that fails, if another process
    // is already publishing to it, or if the file is not one this code wrote:
    // the sidecar is optional, and its absence must never keep a db from
    // opening or cost the operator an unrelated file.
    static std::optional<DbStatsPublisher>
    create(std::filesystem::path const &path);

    DbStatsPublisher(DbStatsPublisher const &) = delete;
    DbStatsPublisher &operator=(DbStatsPublisher const &) = delete;
    DbStatsPublisher(DbStatsPublisher &&other) noexcept;
    ~DbStatsPublisher();

    void
    publish_update_stats(detail::TrieUpdateCollectedStats const &s) noexcept;
};

class DbStatsReader
{
    // Mapped read-only; non-const only so the seqlock can be read through
    // std::atomic_ref, which does not bind to const.
    detail::db_stats_shm *shm_{nullptr};

    explicit DbStatsReader(detail::db_stats_shm *const shm) noexcept
        : shm_{shm}
    {
    }

public:
    // Maps `path` read-only. Returns nullopt if it is absent, too small to
    // hold a header, or not a sidecar of a layout this build understands.
    static std::optional<DbStatsReader> open(std::filesystem::path const &path);

    DbStatsReader(DbStatsReader const &) = delete;
    DbStatsReader &operator=(DbStatsReader const &) = delete;
    DbStatsReader(DbStatsReader &&other) noexcept;
    ~DbStatsReader();

    // nullopt if the writer predates the section, or if a publish kept
    // overwriting it for the whole retry budget.
    std::optional<detail::TrieUpdateCollectedStats>
    read_update_stats() const noexcept;
};

MONAD_MPT_NAMESPACE_END
