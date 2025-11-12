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

#include <ankerl/unordered_dense.h>

MONAD_NAMESPACE_BEGIN

// YP 6.1
class AccountSubstate
{
    template <class Key>
    using Set = ankerl::unordered_dense::set<Key>;

    bool destructed_{false}; // A_s
    bool touched_{false}; // A_t
    bool accessed_{false}; // A_a
    Set<bytes32_t> accessed_storage_{}; // A_K

public:
    AccountSubstate() = default;
    AccountSubstate(AccountSubstate &&) = default;
    AccountSubstate(AccountSubstate const &) = default;
    AccountSubstate &operator=(AccountSubstate &&) = default;
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
    Set<bytes32_t> const &get_accessed_storage() const
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
        bool const inserted = accessed_storage_.emplace(key).second;
        if (inserted) {
            return EVMC_ACCESS_COLD;
        }
        return EVMC_ACCESS_WARM;
    }
};

MONAD_NAMESPACE_END
