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

#include <category/execution/ethereum/metrics/state_access_timer.hpp>

#include <chrono>
#include <format>
#include <mutex>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace
{
    std::mutex g_registry_mutex;
    std::vector<StateAccessTiming *> g_registry;

    // Estimate the cost of a single steady_clock::now() pair so the reader can
    // mentally subtract it from the sub-microsecond (warm / db_cache) buckets.
    uint64_t measure_clock_overhead_ns()
    {
        constexpr int iters = 200'000;
        auto const t0 = std::chrono::steady_clock::now();
        std::chrono::steady_clock::time_point last = t0;
        for (int i = 0; i < iters; ++i) {
            last = std::chrono::steady_clock::now();
        }
        auto const elapsed =
            std::chrono::duration_cast<std::chrono::nanoseconds>(last - t0)
                .count();
        return static_cast<uint64_t>(elapsed) / static_cast<uint64_t>(iters);
    }

    void append_bucket(
        std::string &out, char const *const name, TimingBucket const &b)
    {
        double const avg =
            b.count ? static_cast<double>(b.total_ns) /
                          static_cast<double>(b.count)
                    : 0.0;
        out += std::format(
            "    {:<28} count={:>12}  avg={:>9.1f} ns  total={:>10.3f} ms\n",
            name,
            b.count,
            avg,
            static_cast<double>(b.total_ns) / 1e6);
    }
}

StateAccessTiming &tls_state_access_timing()
{
    // One leaked instance per thread, living to program end so the registry
    // pointer stays valid for the end-of-run summation.
    thread_local StateAccessTiming *const t = [] {
        auto *const p = new StateAccessTiming();
        std::lock_guard<std::mutex> const lk{g_registry_mutex};
        g_registry.push_back(p);
        return p;
    }();
    return *t;
}

std::string report_state_access_timing()
{
    if constexpr (!k_collect_state_access_timing) {
        return {};
    }

    StateAccessTiming agg;
    {
        std::lock_guard<std::mutex> const lk{g_registry_mutex};
        for (auto const *const t : g_registry) {
            agg.sload_warm.merge(t->sload_warm);
            agg.sload_cold_block_local.merge(t->sload_cold_block_local);
            agg.sload_cold_db_cache.merge(t->sload_cold_db_cache);
            agg.sload_cold_disk.merge(t->sload_cold_disk);
            agg.sstore_warm.merge(t->sstore_warm);
            agg.sstore_cold_block_local.merge(t->sstore_cold_block_local);
            agg.sstore_cold_db_cache.merge(t->sstore_cold_db_cache);
            agg.sstore_cold_disk.merge(t->sstore_cold_disk);
            agg.account_block_local.merge(t->account_block_local);
            agg.account_db_cache.merge(t->account_db_cache);
            agg.account_disk.merge(t->account_disk);
        }
    }

    std::string out = "\n=== state access timing (1 gas ~= 1 ns) ===\n";
    out += std::format(
        "  clock overhead ~= {} ns/measurement (subtract from sub-us buckets)\n",
        measure_clock_overhead_ns());
    out += "  NOTE: 'disk' avg is wall-clock and is inflated when nfibers>1 "
           "(the fiber yields and the thread runs other work during the read); "
           "rerun with nfibers=1 for a clean disk latency.\n";

    out += "  SLOAD (State::get_storage):\n";
    append_bucket(out, "warm (tx-local)", agg.sload_warm);
    append_bucket(out, "cold block-local (mem)", agg.sload_cold_block_local);
    append_bucket(out, "cold db_cache (LRU hit)", agg.sload_cold_db_cache);
    append_bucket(out, "cold disk (LRU miss)", agg.sload_cold_disk);

    out += "  SSTORE (original-value load):\n";
    append_bucket(out, "warm (tx-local)", agg.sstore_warm);
    append_bucket(out, "cold block-local (mem)", agg.sstore_cold_block_local);
    append_bucket(out, "cold db_cache (LRU hit)", agg.sstore_cold_db_cache);
    append_bucket(out, "cold disk (LRU miss)", agg.sstore_cold_disk);

    out += "  ACCOUNT (cold value materialization):\n";
    append_bucket(out, "block-local (mem)", agg.account_block_local);
    append_bucket(out, "db_cache (LRU hit)", agg.account_db_cache);
    append_bucket(out, "disk (LRU miss)", agg.account_disk);

    return out;
}

MONAD_NAMESPACE_END
