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

#include <category/core/assert.h>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/monad/db/cache_pricing.hpp>

#include <algorithm>
#include <cstdlib>
#include <cstring>

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

byte_string cache_pricing_account_key(bytes32_t const &hashed_address)
{
    byte_string key(1 + sizeof(hashed_address.bytes), 0);
    key[0] = CACHE_PRICING_ACCOUNT_ENTRY;
    std::memcpy(
        key.data() + 1, hashed_address.bytes, sizeof(hashed_address.bytes));
    return key;
}

byte_string
cache_pricing_storage_key(Address const &address, bytes32_t const &lookup_key)
{
    unsigned char buf[sizeof(address.bytes) + sizeof(lookup_key.bytes)];
    std::memcpy(buf, address.bytes, sizeof(address.bytes));
    std::memcpy(
        buf + sizeof(address.bytes),
        lookup_key.bytes,
        sizeof(lookup_key.bytes));
    auto const hashed = keccak256({buf, sizeof(buf)});
    byte_string key(1 + sizeof(hashed.bytes), 0);
    key[0] = CACHE_PRICING_STORAGE_ENTRY;
    std::memcpy(key.data() + 1, hashed.bytes, sizeof(hashed.bytes));
    return key;
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

void PricingHistogram::seed(Db &db, uint64_t const block)
{
    for (auto const kind : {PricingKind::account, PricingKind::storage}) {
        auto const read = [&](uint64_t const b) {
            return kind == PricingKind::account
                       ? db.read_account_pricing_bucket(b)
                       : db.read_storage_pricing_bucket(b);
        };
        auto const oldest = read(CACHE_PRICING_META_BUCKET);
        if (!oldest.has_value()) {
            continue;
        }
        uint64_t const window_floor =
            block > CACHE_PRICING_WINDOW ? block - CACHE_PRICING_WINDOW : 0;
        auto &buckets = buckets_[static_cast<size_t>(kind)];
        for (uint64_t b = std::max(window_floor, *oldest); b < block; ++b) {
            if (auto const w = read(b); w.value_or(0) > 0) {
                buckets[b] = *w;
            }
        }
    }
}

void PricingHistogram::apply(
    PricingBucketDeltas const &deltas, uint64_t const block)
{
    for (auto const &[bucket, delta] : deltas) {
        auto const [kind, b] = bucket;
        if (b == CACHE_PRICING_META_BUCKET || delta == 0) {
            continue;
        }
        auto &buckets = buckets_[static_cast<size_t>(kind)];
        auto const it = buckets.try_emplace(b, 0).first;
        int64_t const weight = static_cast<int64_t>(it->second) + delta;
        MONAD_ASSERT(weight >= 0);
        if (weight == 0) {
            buckets.erase(it);
        }
        else {
            it->second = static_cast<uint64_t>(weight);
        }
    }
    if (block > CACHE_PRICING_WINDOW) {
        uint64_t const window_floor = block - CACHE_PRICING_WINDOW;
        for (auto &buckets : buckets_) {
            buckets.erase(buckets.begin(), buckets.lower_bound(window_floor));
        }
    }
}

PricingCutoffs PricingHistogram::cutoffs(uint64_t const block) const
{
    // same walk as cutoff() above; absent buckets contribute nothing, so
    // only live buckets are visited. The floor is the oldest live bucket
    // rather than the meta marker; when the two differ no live entry has a
    // last_access in between, so the priced set is the same.
    auto const walk = [block](
                          std::map<uint64_t, uint64_t> const &buckets,
                          uint64_t const capacity) {
        if (buckets.empty()) {
            return block == 0 ? uint64_t{0} : block - 1;
        }
        uint64_t const window_floor =
            block > CACHE_PRICING_WINDOW ? block - CACHE_PRICING_WINDOW : 0;
        uint64_t const floor = std::max(window_floor, buckets.begin()->first);
        uint64_t sum = 0;
        for (auto it = buckets.lower_bound(block); it != buckets.begin();) {
            --it;
            if (it->first < floor) {
                break;
            }
            sum += it->second;
            if (sum > capacity) {
                return it->first;
            }
        }
        return floor == 0 ? uint64_t{0} : floor - 1;
    };
    return {
        .account = walk(
            buckets_[static_cast<size_t>(PricingKind::account)],
            CACHE_PRICING_ACCOUNT_CAPACITY),
        .storage = walk(
            buckets_[static_cast<size_t>(PricingKind::storage)],
            CACHE_PRICING_STORAGE_SLOT_CAPACITY)};
}

MONAD_NAMESPACE_END
