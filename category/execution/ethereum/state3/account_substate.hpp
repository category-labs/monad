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
#include <category/vm/evm/access_status.h>

#include <cstdint>
#include <vector>

MONAD_NAMESPACE_BEGIN

// Preload the key's last word for linear scans. Small big-endian keys differ
// there; preloading all four words measured worse.
[[nodiscard]] inline std::uint64_t key_tail(bytes32_t const &k)
{
    std::uint64_t w;
    __builtin_memcpy(&w, k.bytes + 24, 8);
    // Keep the tail load outside the scan and prevent GCC from folding the
    // comparisons back into an address-order memcmp. Not a memory barrier.
    __asm__("" : "+r"(w));
    return w;
}

// Compare search key k with entry key e; tail must be key_tail(k).
// Check words 0 and 3 first to reject most mismatches early,
// then words 1 and 2 to confirm equality.
[[nodiscard]] inline bool
key_equals(bytes32_t const &k, std::uint64_t const tail, bytes32_t const &e)
{
    std::uint64_t a, b;
    __builtin_memcpy(&a, e.bytes, 8);
    __builtin_memcpy(&b, k.bytes, 8);
    if (a != b) {
        return false;
    }
    __builtin_memcpy(&a, e.bytes + 24, 8);
    if (a != tail) {
        return false;
    }
    __builtin_memcpy(&a, e.bytes + 8, 8);
    __builtin_memcpy(&b, k.bytes + 8, 8);
    if (a != b) {
        return false;
    }
    __builtin_memcpy(&a, e.bytes + 16, 8);
    __builtin_memcpy(&b, k.bytes + 16, 8);
    return a == b;
}

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
    monad_access_status access()
    {
        bool const inserted = !accessed_;
        accessed_ = true;
        if (inserted) {
            return MONAD_ACCESS_COLD;
        }
        return MONAD_ACCESS_WARM;
    }

    // A_K
    monad_access_status access_storage(bytes32_t const &key)
    {
        std::uint64_t const tail = key_tail(key);
        for (auto const &k : accessed_storage_) {
            if (key_equals(key, tail, k)) {
                return MONAD_ACCESS_WARM;
            }
        }
        accessed_storage_.push_back(key);
        return MONAD_ACCESS_COLD;
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
