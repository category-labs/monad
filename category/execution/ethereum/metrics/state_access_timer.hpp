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

// Latency instrumentation for the storage / account read path, used to inform
// gas pricing (the working assumption is 1 gas ~= 1 ns). It measures the
// wall-clock cost of materializing a value for SLOAD, the SSTORE original-value
// load, and cold account loads, bucketed by *where* the value came from:
//
//   warm        - tx-local State map hit (EIP-2929 warm); no block/db touch
//   block_local - in-memory block StateDeltas hit (or negative lookup); no disk
//   db_cache    - in-memory db_cache (LRU) hit; no disk I/O
//   disk        - db_cache miss -> async disk read
//
// db_cache latency is the empirical anchor for the MIP "cached" access price
// (CACHED_LOAD_COST=800 storage / CACHED_ACCOUNT_ACCESS_GAS=500); disk latency
// anchors the full cold price (8100 storage / 10100 account).
//
// Threading: each worker thread accumulates into its own thread-local struct
// (no atomics on the hot path); the per-thread structs are registered in a
// global list and summed once at end of run. Fibers on a single thread are
// cooperative, so non-atomic accumulation is race-free within a thread.

#include <category/core/config.hpp>

#include <chrono>
#include <cstdint>
#include <string>

MONAD_NAMESPACE_BEGIN

// Compile-time master switch. Default on for this pricing-experiment worktree;
// flip to false (and rebuild) for clean throughput runs with zero overhead.
inline constexpr bool k_collect_state_access_timing = true;

// Where a value was ultimately served from. The deepest layer that resolves a
// read records this; the State layer reads it back immediately after the
// (synchronous) return chain, with no fiber yield in between.
enum class ReadSource : uint8_t
{
    block_local = 0, // in-memory block StateDeltas, or a negative lookup
    db_cache = 1, // in-memory db_cache (LRU) hit; no disk I/O
    disk = 2, // db_cache miss -> async disk read
};

namespace detail
{
    inline thread_local ReadSource tls_last_read_source = ReadSource::block_local;
}

inline void set_last_read_source(ReadSource const s) noexcept
{
    if constexpr (k_collect_state_access_timing) {
        detail::tls_last_read_source = s;
    }
}

inline ReadSource last_read_source() noexcept
{
    return detail::tls_last_read_source;
}

struct TimingBucket
{
    uint64_t count{0};
    uint64_t total_ns{0};

    void record(uint64_t const ns) noexcept
    {
        ++count;
        total_ns += ns;
    }

    void merge(TimingBucket const &o) noexcept
    {
        count += o.count;
        total_ns += o.total_ns;
    }
};

// One instance per worker thread (thread-local), summed at end of run.
struct StateAccessTiming
{
    // SLOAD: full State::get_storage value materialization.
    TimingBucket sload_warm;
    TimingBucket sload_cold_block_local;
    TimingBucket sload_cold_db_cache;
    TimingBucket sload_cold_disk;

    // SSTORE: original-value load in State::set_storage.
    TimingBucket sstore_warm;
    TimingBucket sstore_cold_block_local;
    TimingBucket sstore_cold_db_cache;
    TimingBucket sstore_cold_disk;

    // Cold account value materialization (block_state_.read_account). There is
    // no "warm" account bucket here: a warm account access is an access-set hit
    // that materializes no value (cost ~= warm SLOAD).
    TimingBucket account_block_local;
    TimingBucket account_db_cache;
    TimingBucket account_disk;
};

// Returns this thread's accumulator, registering it on first use.
StateAccessTiming &tls_state_access_timing();

// Sums all threads' accumulators and formats a human-readable report.
std::string report_state_access_timing();

// RAII timer: starts a steady_clock on construction, records the elapsed time
// into a target bucket on destruction. The body defaults to the "warm" bucket;
// callers move it to the appropriate cold bucket once the read source is known.
class ScopedAccessTimer
{
public:
    enum class Op : uint8_t
    {
        sload,
        sstore
    };

    explicit ScopedAccessTimer(Op const op) noexcept
    {
        if constexpr (k_collect_state_access_timing) {
            auto &t = tls_state_access_timing();
            bucket_ = (op == Op::sload) ? &t.sload_warm : &t.sstore_warm;
            tls_ = &t;
            op_ = op;
            start_ = std::chrono::steady_clock::now();
        }
    }

    // Reclassify to the cold bucket matching the (just-resolved) read source.
    void classify_cold(ReadSource const s) noexcept
    {
        if constexpr (k_collect_state_access_timing) {
            bucket_ = cold_bucket(*tls_, op_, s);
        }
    }

    ~ScopedAccessTimer()
    {
        if constexpr (k_collect_state_access_timing) {
            auto const ns =
                std::chrono::duration_cast<std::chrono::nanoseconds>(
                    std::chrono::steady_clock::now() - start_)
                    .count();
            bucket_->record(static_cast<uint64_t>(ns));
        }
    }

    ScopedAccessTimer(ScopedAccessTimer const &) = delete;
    ScopedAccessTimer &operator=(ScopedAccessTimer const &) = delete;

private:
    static TimingBucket *
    cold_bucket(StateAccessTiming &t, Op const op, ReadSource const s) noexcept
    {
        if (op == Op::sload) {
            switch (s) {
            case ReadSource::block_local:
                return &t.sload_cold_block_local;
            case ReadSource::db_cache:
                return &t.sload_cold_db_cache;
            case ReadSource::disk:
                return &t.sload_cold_disk;
            }
        }
        else {
            switch (s) {
            case ReadSource::block_local:
                return &t.sstore_cold_block_local;
            case ReadSource::db_cache:
                return &t.sstore_cold_db_cache;
            case ReadSource::disk:
                return &t.sstore_cold_disk;
            }
        }
        return &t.sload_cold_block_local; // unreachable
    }

    TimingBucket *bucket_{nullptr};
    StateAccessTiming *tls_{nullptr};
    Op op_{Op::sload};
    std::chrono::steady_clock::time_point start_{};
};

// Records a cold account value materialization (no warm/RAII variant needed:
// the call site wraps exactly the block_state_.read_account() call).
inline void
record_account_load(std::chrono::steady_clock::duration const d) noexcept
{
    if constexpr (k_collect_state_access_timing) {
        auto &t = tls_state_access_timing();
        auto const ns =
            std::chrono::duration_cast<std::chrono::nanoseconds>(d).count();
        switch (last_read_source()) {
        case ReadSource::block_local:
            t.account_block_local.record(static_cast<uint64_t>(ns));
            break;
        case ReadSource::db_cache:
            t.account_db_cache.record(static_cast<uint64_t>(ns));
            break;
        case ReadSource::disk:
            t.account_disk.record(static_cast<uint64_t>(ns));
            break;
        }
    }
}

MONAD_NAMESPACE_END
