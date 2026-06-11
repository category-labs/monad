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
#include <category/core/int.hpp>
#include <category/vm/host.hpp>

#include <evmc/evmc.h>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Warray-bounds"
#include <immer/map.hpp>
#pragma GCC diagnostic pop

MONAD_NAMESPACE_BEGIN

// This is temp. Will be removed after the storage_page PR is merged.
namespace detail
{
    inline bytes32_t compute_page_key(bytes32_t const &storage_key)
    {
        constexpr size_t PAGE_KEY_SHIFT = 7;
        return store_be_as<bytes32_t>(
            load_be<uint256_t>(storage_key) >> PAGE_KEY_SHIFT);
    }
}

class PageTracker
{
    struct PageState
    {
        bool accessed{false}; // read
        bool dirty{false}; // write
        int16_t peak_growth{0};
        int16_t current_growth{0};
    };

    using PageMap = immer::map<
        bytes32_t, PageState, ankerl::unordered_dense::hash<monad::bytes32_t>>;

    PageMap pages_{};

    PageState lookup_page_state(bytes32_t const &page_key) const
    {
        auto const *cur = pages_.find(page_key);
        return cur ? *cur : PageState{};
    }

public:
    evmc_access_status access_page(bytes32_t const &key)
    {
        auto const pkey = detail::compute_page_key(key);
        PageState s = lookup_page_state(pkey);
        if (s.accessed) {
            return EVMC_ACCESS_WARM;
        }
        s.accessed = true;
        pages_ = pages_.set(pkey, s);
        return EVMC_ACCESS_COLD;
    }

    vm::Host::PageStorageStatus
    update_page(bytes32_t const &key, evmc_storage_status status)
    {
        auto const pkey = detail::compute_page_key(key);
        PageState ps = lookup_page_state(pkey);

        bool const value_changed = (status != EVMC_STORAGE_ASSIGNED);
        bool first_page_write = false;
        if (!ps.dirty) {
            first_page_write = value_changed;
            ps.dirty = value_changed;
        }

        switch (status) {
        case EVMC_STORAGE_ADDED:
        case EVMC_STORAGE_DELETED_ADDED:
        case EVMC_STORAGE_DELETED_RESTORED:
            ++ps.current_growth;
            break;
        case EVMC_STORAGE_DELETED:
        case EVMC_STORAGE_MODIFIED_DELETED:
        case EVMC_STORAGE_ADDED_DELETED:
            --ps.current_growth;
            break;
        default:
            break;
        }

        bool const grew_state = ps.current_growth > ps.peak_growth;
        if (grew_state) {
            ps.peak_growth = ps.current_growth;
        }
        if (value_changed) {
            pages_ = pages_.set(pkey, ps);
        }

        return {first_page_write, grew_state};
    }
};

MONAD_NAMESPACE_END
