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

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Warray-bounds"
#include <immer/set.hpp>
#pragma GCC diagnostic pop

MONAD_NAMESPACE_BEGIN

// YP 6.1
class AccountSubstate
{
    using Set =
        immer::set<bytes32_t, ankerl::unordered_dense::hash<monad::bytes32_t>>;

    bool destructed_{false}; // A_s
    bool touched_{false}; // A_t
    bool accessed_{false}; // A_a
    Set accessed_storage_{}; // A_K

public:
    AccountSubstate() = default;
    AccountSubstate(AccountSubstate &&) noexcept = default;
    AccountSubstate(AccountSubstate const &) = default;
    AccountSubstate &operator=(AccountSubstate &&) noexcept = default;
    AccountSubstate &operator=(AccountSubstate const &) = default;

    // A_s
    bool is_destructed() const
    {
        return destructed_;
    }

    // A_t
    bool is_touched() const
    {
        return touched_;
    }

    // A_K
    Set get_accessed_storage() const
    {
        return accessed_storage_;
    }

    // A_s
    bool destruct()
    {
        bool const inserted = !destructed_;
        destructed_ = true;
        return inserted;
    }

    // A_t
    void touch()
    {
        touched_ = true;
    }

    // A_a
    evmc_access_status access()
    {
        bool const inserted = !accessed_;
        accessed_ = true;
        if (inserted) {
            return EVMC_ACCESS_COLD;
        }
        return EVMC_ACCESS_WARM;
    }

    // A_K
    evmc_access_status access_storage(bytes32_t const &key)
    {
        if (accessed_storage_.count(key) == 0) {
            accessed_storage_ = accessed_storage_.insert(key);
            return EVMC_ACCESS_COLD;
        }
        return EVMC_ACCESS_WARM;
    }
};

static_assert(sizeof(AccountSubstate) == 24);

MONAD_NAMESPACE_END
