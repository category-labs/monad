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

#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/monad/db/cache_pricing.hpp>

#include <algorithm>
#include <cstdlib>

MONAD_NAMESPACE_BEGIN

uint64_t cache_pricing_update_interval()
{
    static uint64_t const interval = [] {
        char const *const env = std::getenv("MONAD_MBC_C");
        return env != nullptr ? std::strtoull(env, nullptr, 10)
                              : CACHE_PRICING_UPDATE_INTERVAL;
    }();
    return interval;
}

byte_string
cache_pricing_bucket_key(PricingKind const kind, uint64_t const block)
{
    byte_string key(9, 0);
    key[0] = static_cast<unsigned char>(kind);
    for (unsigned i = 0; i < 8; ++i) {
        key[1 + i] = static_cast<unsigned char>(block >> (56 - 8 * i));
    }
    return key;
}

namespace
{
    uint64_t cutoff(
        Db &db, PricingKind const kind, uint64_t const block,
        uint64_t const capacity)
    {
        auto const read = [&](uint64_t const b) {
            return kind == PricingKind::account
                       ? db.read_account_pricing_bucket(b)
                       : db.read_storage_pricing_bucket(b);
        };
        // bucket 0 holds the oldest live bucket block (real buckets are >= 1);
        // absent means no bucket has ever been written
        auto const oldest = read(CACHE_PRICING_META_BUCKET);
        if (!oldest.has_value()) {
            return block == 0 ? 0 : block - 1;
        }
        uint64_t const window_floor =
            block > CACHE_PRICING_WINDOW ? block - CACHE_PRICING_WINDOW : 0;
        uint64_t const floor = std::max(window_floor, *oldest);
        uint64_t sum = 0;
        for (uint64_t b = block; b-- > floor;) {
            sum += read(b).value_or(0);
            if (sum > capacity) {
                return b;
            }
        }
        return floor == 0 ? 0 : floor - 1;
    }
}

PricingCutoffs compute_pricing_cutoffs(Db &db, uint64_t const block)
{
    return {
        .account = cutoff(
            db, PricingKind::account, block, CACHE_PRICING_ACCOUNT_CAPACITY),
        .storage = cutoff(
            db,
            PricingKind::storage,
            block,
            CACHE_PRICING_STORAGE_SLOT_CAPACITY)};
}

MONAD_NAMESPACE_END
