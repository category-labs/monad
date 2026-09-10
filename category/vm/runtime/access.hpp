// Copyright (C) 2026 Category Labs, Inc.
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

// Dynamic surcharges for account/storage first accesses. Pre multi-block
// cache: cold or nothing (warm). With multi_block_cache_active, a first
// access to state whose last_access is within the priced window charges the
// intermediate cached cost instead of cold.

#include <category/vm/evm/traits.hpp>
#include <category/vm/host.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.hpp>

#include <atomic>

namespace monad::vm::runtime
{
    // Shadow measurement (evm traits experiment): accesses the multi-block
    // cache would have priced "cached" are counted here while the original
    // cold cost is still charged, keeping the execution trace identical.
    struct CacheShadowStats
    {
        std::atomic<uint64_t> cached_accounts{0};
        std::atomic<uint64_t> cached_storage{0};
        std::atomic<uint64_t> saved_gas{0};
        // stamp-record volume (filled by the commit builder)
        std::atomic<uint64_t> account_stamp_records{0};
        std::atomic<uint64_t> storage_stamp_records{0};
        // first (non-warm) accesses per block and how many hit no trie leaf
        std::atomic<uint64_t> first_accounts{0};
        std::atomic<uint64_t> missing_accounts{0};
        std::atomic<uint64_t> first_storage{0};
        std::atomic<uint64_t> missing_storage{0};
        // inter-touch gap (block - stamp) of stamped items at their first
        // access: buckets <=100, <=250, <=500, <=1000, <=2000, >2000
        static constexpr uint64_t GAP_BOUNDS[] = {100, 250, 500, 1000, 2000};
        std::atomic<uint64_t> account_gaps[6]{};
        std::atomic<uint64_t> storage_gaps[6]{};

        static void
        record_gap(std::atomic<uint64_t> (&buckets)[6], uint64_t const gap)
        {
            size_t i = 0;
            while (i < 5 && gap > GAP_BOUNDS[i]) {
                ++i;
            }
            buckets[i].fetch_add(1, std::memory_order_relaxed);
        }
    };

    inline CacheShadowStats g_cache_shadow_stats;

    template <Traits traits>
    [[gnu::always_inline]] inline int64_t
    account_access_cost(Context *ctx, evmc::address const &address) noexcept
    {
        if constexpr (traits::multi_block_cache_active()) {
            auto *const host = evmc::Host::from_context<vm::Host>(ctx->context);
            switch (host->access_account_tier(address)) {
            case Host::AccessTier::cold:
                return traits::cold_account_cost();
            case Host::AccessTier::cached:
                if constexpr (is_evm_trait_v<traits>) {
                    g_cache_shadow_stats.cached_accounts.fetch_add(
                        1, std::memory_order_relaxed);
                    g_cache_shadow_stats.saved_gas.fetch_add(
                        static_cast<uint64_t>(
                            traits::cold_account_cost() -
                            traits::cached_account_cost()),
                        std::memory_order_relaxed);
                    return traits::cold_account_cost();
                }
                else {
                    return traits::cached_account_cost();
                }
            case Host::AccessTier::warm:
                return 0;
            }
            return traits::cold_account_cost(); // unreachable
        }
        else {
            return ctx->host->access_account(ctx->context, &address) ==
                           EVMC_ACCESS_COLD
                       ? traits::cold_account_cost()
                       : 0;
        }
    }

    template <Traits traits>
    [[gnu::always_inline]] inline int64_t storage_access_cost(
        Context *ctx, evmc::address const &address,
        evmc::bytes32 const &key) noexcept
    {
        if constexpr (traits::multi_block_cache_active()) {
            auto *const host = evmc::Host::from_context<vm::Host>(ctx->context);
            switch (host->access_storage_tier(address, key)) {
            case Host::AccessTier::cold:
                return traits::cold_storage_cost();
            case Host::AccessTier::cached:
                if constexpr (is_evm_trait_v<traits>) {
                    g_cache_shadow_stats.cached_storage.fetch_add(
                        1, std::memory_order_relaxed);
                    g_cache_shadow_stats.saved_gas.fetch_add(
                        static_cast<uint64_t>(
                            traits::cold_storage_cost() -
                            traits::cached_storage_cost()),
                        std::memory_order_relaxed);
                    return traits::cold_storage_cost();
                }
                else {
                    return traits::cached_storage_cost();
                }
            case Host::AccessTier::warm:
                return 0;
            }
            return traits::cold_storage_cost(); // unreachable
        }
        else {
            return ctx->host->access_storage(ctx->context, &address, &key) ==
                           EVMC_ACCESS_COLD
                       ? traits::cold_storage_cost()
                       : 0;
        }
    }
}
