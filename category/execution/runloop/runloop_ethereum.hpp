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

#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/monad/db/cache_pricing.hpp>
#include <category/vm/vm.hpp>

#include <cstdint>
#include <filesystem>
#include <utility>

#include <signal.h>

MONAD_NAMESPACE_BEGIN

// Fixed-window cache run totals of the measurement arm (committed
// transactions only), printed by main at the end of the run.
struct MbcRunTotals : CacheTierStats
{
    uint64_t account_stamps{0};
    uint64_t storage_stamps{0};
    // page-encoding emulation and empty-read classification, summed over
    // the blocks' StampBlockStats
    uint64_t probed_pages{0};
    uint64_t occupancy_buckets[5]{};
    uint64_t empty_on_live_page{0};
    uint64_t empty_page{0};
    uint64_t empty_unprobed{0};
    uint64_t sampled_live{0};
    uint64_t sampled_empty{0};
    uint64_t negative_stamps_selected{0};
    uint64_t emulated_cap_hits{0};

    void add_block(StampBlockStats const &st)
    {
        probed_pages += st.probed_pages;
        for (size_t i = 0; i < 5; ++i) {
            occupancy_buckets[i] += st.occupancy_buckets[i];
        }
        empty_on_live_page += st.empty_on_live_page;
        empty_page += st.empty_page;
        empty_unprobed += st.empty_unprobed;
        sampled_live += st.sampled_live;
        sampled_empty += st.sampled_empty;
        negative_stamps_selected += st.negative_stamps_selected;
        emulated_cap_hits += st.emulated_cap_hit ? 1 : 0;
    }
};

extern MbcRunTotals g_mbc_totals;

struct Chain;
struct Db;
class BlockHashBufferFinalized;
class ExecutionEventRecorder;

namespace fiber
{
    class PriorityPool;
}

Result<std::pair<uint64_t, uint64_t>> runloop_ethereum(
    Chain const &, std::filesystem::path const &, Db &, vm::VM &,
    BlockHashBufferFinalized &, fiber::PriorityPool &, uint64_t &, uint64_t,
    sig_atomic_t const volatile &, bool enable_tracing,
    ExecutionEventRecorder *, std::filesystem::path const &rlp_path = {});

MONAD_NAMESPACE_END
