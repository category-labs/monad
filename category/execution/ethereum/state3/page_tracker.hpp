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

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>

#include <evmc/evmc.h>

// TODO immer known to trigger incorrect warning
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Warray-bounds"
#include <immer/map.hpp>
#include <immer/set.hpp>
#pragma GCC diagnostic pop

MONAD_NAMESPACE_BEGIN

class PageTracker
{
    using Set =
        immer::set<bytes32_t, ankerl::unordered_dense::hash<monad::bytes32_t>>;

    struct SlotCounters
    {
        int32_t delta{0};
        int32_t max_nonzero{0};
    };

    using CounterMap = immer::map<
        bytes32_t, SlotCounters,
        ankerl::unordered_dense::hash<monad::bytes32_t>>;

    Set write_accessed_pages_{};
    CounterMap slot_counters_{};

public:
    struct Result
    {
        bool write_page_cold;
        bool exceeded_max;
    };

    Result update(bytes32_t const &page_key, evmc_storage_status status)
    {
        bool const value_changed = (status != EVMC_STORAGE_ASSIGNED);
        bool write_page_cold = false;
        if (value_changed) {
            if (write_accessed_pages_.count(page_key) == 0) {
                write_accessed_pages_ = write_accessed_pages_.insert(page_key);
                write_page_cold = true;
            }
        }

        int32_t adjustment = 0;
        switch (status) {
        case EVMC_STORAGE_ADDED:
        case EVMC_STORAGE_DELETED_ADDED:
        case EVMC_STORAGE_DELETED_RESTORED:
            adjustment = +1;
            break;
        case EVMC_STORAGE_DELETED:
        case EVMC_STORAGE_MODIFIED_DELETED:
        case EVMC_STORAGE_ADDED_DELETED:
            adjustment = -1;
            break;
        default:
            break;
        }

        bool exceeded_max = false;
        if (adjustment != 0) {
            auto const *cur = slot_counters_.find(page_key);
            SlotCounters counters = cur ? *cur : SlotCounters{};
            counters.delta += adjustment;

            if (adjustment > 0 && counters.delta > counters.max_nonzero) {
                counters.max_nonzero = counters.delta;
                exceeded_max = true;
            }

            slot_counters_ = slot_counters_.set(page_key, counters);
        }

        return {write_page_cold, exceeded_max};
    }
};

MONAD_NAMESPACE_END
