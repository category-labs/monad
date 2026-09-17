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

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>

#include <evmc/evmc.h>

#include <vector>

MONAD_NAMESPACE_BEGIN

// YP 6.1
class AccountSubstate
{
    // Warm-slot sets are typically small: linear lookup avoids hashing.
    using Set = std::vector<bytes32_t>;

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
    Set const &get_accessed_storage() const
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

    // A_t. Returns true only on transition, so the journal records it once.
    bool touch()
    {
        bool const inserted = !touched_;
        touched_ = true;
        return inserted;
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
        for (auto const &k : accessed_storage_) {
            if (__builtin_memcmp(k.bytes, key.bytes, sizeof(key.bytes)) == 0) {
                return EVMC_ACCESS_WARM;
            }
        }
        accessed_storage_.push_back(key);
        return EVMC_ACCESS_COLD;
    }

    // Undo operations, for the journal only. Each reverses exactly one
    // journalled transition.
    void undo_touched()
    {
        touched_ = false;
    }

    void undo_destructed()
    {
        destructed_ = false;
    }

    void undo_accessed()
    {
        accessed_ = false;
    }

    // Warm slots are appended; reverse replay must remove the last key.
    void undo_warm_slot(bytes32_t const &key)
    {
        MONAD_ASSERT(!accessed_storage_.empty());
        MONAD_ASSERT(
            __builtin_memcmp(
                accessed_storage_.back().bytes, key.bytes, sizeof(key.bytes)) ==
            0);
        accessed_storage_.pop_back();
    }
};

// Guard against unintended growth of the per-account substate.
static_assert(sizeof(AccountSubstate) == 32);

MONAD_NAMESPACE_END
