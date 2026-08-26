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
    // A_K held an immer::set. Persistence was not wanted for its own sake: it was what made
    // VersionStack's per-frame copy of this row O(1). The undo log replaced that copy, and the
    // set is small enough that the log's own copy of the row stays cheap -- 4,459 warm slots
    // across 1,392 accounts a block, so ~3 keys each. At that size a linear scan of 32-byte keys
    // beats hashing one, and the container is a vector.
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

    // A_t. Returns whether this call is what set it: the journal records a transition, not a
    // write, so a second touch() in the same frame must add no entry.
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

    // Undo operations, for the journal only. Each reverses exactly one journalled transition.
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

    // A_K is append-only apart from this, so within one row the journal's records for it are in
    // append order, and a backwards replay always removes the last one. The assert states that
    // invariant rather than trusting it -- an erase from the middle would leave the remaining
    // records pointing at the wrong entries.
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

// 24 while A_K was an 8-byte persistent handle; a vector is 24 on its own. The number is here to
// catch growth nobody intended, so it moves with a change that was intended.
static_assert(sizeof(AccountSubstate) == 32);

MONAD_NAMESPACE_END
