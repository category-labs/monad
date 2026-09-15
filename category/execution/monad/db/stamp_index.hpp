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

#include <ankerl/unordered_dense.h>
#include <category/core/assert.h>
#include <category/execution/monad/db/cache_pricing.hpp>
#include <deque>
#include <limits>

MONAD_NAMESPACE_BEGIN

// Finalized key history, independent of value-cache residency. Updated only
// during serialized finalization/bootstrap; execution performs const lookups.
// The FIFO includes renewals so advancing the ring floor retires history
// incrementally, without scanning the entire hash table each block.
template <class Key, class Hash = ankerl::unordered_dense::hash<Key>>
class StampIndex
{
    ankerl::unordered_dense::segmented_map<Key, uint64_t, Hash> stamps_;
    static constexpr uint32_t EMPTY = std::numeric_limits<uint32_t>::max();
    // Absolute record position -> dense-map index, or EMPTY for an older
    // renewal. Four bytes per retained record; keys are stored only once.
    std::deque<uint32_t> records_;
    uint64_t first_{1};
    CacheRingView view_;

public:
    uint64_t find(Key const &key) const
    {
        auto const it = stamps_.find(key);
        return it != stamps_.end() && cache_stamp_cached(it->second, view_)
                   ? it->second
                   : 0;
    }

    template <class Updates>
    void update(CacheRingView const &view, Updates const &updates)
    {
        MONAD_ASSERT(view.floor >= view_.floor);
        MONAD_ASSERT(view.next >= view_.next);
        while (!records_.empty() && first_ < view.floor) {
            auto const index = records_.front();
            if (index != EMPTY) {
                MONAD_ASSERT(index < stamps_.size());
                MONAD_ASSERT(stamps_.values()[index].second == first_);
                // unordered_dense erases by moving its last value into the
                // vacated position. Repair that record's reverse index.
                auto const moved_stamp = stamps_.values().back().second;
                records_[moved_stamp - first_] = index;
                stamps_.erase(stamps_.begin() + index);
            }
            records_.pop_front();
            ++first_;
        }
        if (records_.empty()) {
            first_ = view.floor;
        }
        while (first_ + records_.size() < view.next) {
            records_.push_back(EMPTY);
        }
        view_ = view;
        for (auto const &[key, stamp] : updates) {
            if (!cache_stamp_cached(stamp, view)) {
                continue;
            }
            auto [it, added] = stamps_.try_emplace(key, stamp);
            if (!added && it->second >= stamp) {
                continue;
            }
            if (!added) {
                records_[it->second - first_] = EMPTY;
            }
            it->second = stamp;
            MONAD_ASSERT(stamps_.size() < EMPTY);
            records_[stamp - first_] =
                static_cast<uint32_t>(it - stamps_.begin());
        }
    }

    void clear()
    {
        stamps_.clear();
        records_.clear();
        view_ = {};
        first_ = 1;
    }
};

MONAD_NAMESPACE_END
