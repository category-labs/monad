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

#include <cstdint>
#include <vector>

MONAD_NAMESPACE_BEGIN

// Comparing a 32-byte key inside a linear scan, in the order that decides.
//
// __builtin_memcmp compares in address order, and bytes32_t is big-endian: every slot index
// below 2^64 -- which is every sequentially numbered state variable and array element -- is 24
// zero bytes and then the value. So the entries that survive a scan's first word have words 1
// and 2 zero on both sides, and those two words reject nothing. Measured over the whole guest
// they reject 2.98 % of the entries reaching them, and none at all in get_storage or
// access_storage.
//
// Only word 3 is hoisted out of the scan. Hoisting all four regresses -- measured +0.103 %
// steps, +0.056 % COST over five blocks: the scans are about four entries long, so a four-load
// prologue on every call costs more than the loop saves, and four values live across the loop
// spill in these functions. One load pays for itself on the first entry it rejects.
[[nodiscard]] inline std::uint64_t key_tail(bytes32_t const &k)
{
    std::uint64_t w;
    __builtin_memcpy(&w, k.bytes + 24, 8);
    // Without this the load sinks back into the scan -- key and entry have the same type, so a
    // store to an entry could alias the key -- and once it is there GCC folds the four compares
    // back into the memcmp it already knows, in address order. The constraint is empty and names
    // no memory: it orders nothing, it only denies the optimiser the right to rematerialise this.
    __asm__("" : "+r"(w));
    return w;
}

// Word 0 first: it rejects 62 % on its own, and its key half is already a loop invariant the
// compiler hoists by itself. Then word 3, from `tail`. Words 1 and 2 last, where they cost
// nothing on the entries the first two have already rejected.
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

#ifdef MONAD_ZKVM_ZISK
    // The note above holds at ~3 keys, and the note on key_tail measured the scan at about four
    // entries -- on median blocks. The corpus is not median: over 200 mainnet blocks, 27 of them cost
    // more than 5 % above a competing guest, and on the worst of those access_storage alone is 5.8 %
    // of the block's steps against 0.63 % on a median one. A_K accumulates every slot an account
    // touches for a whole block, so on a storage-heavy contract the scan is the cost, and it is
    // quadratic in the slots touched.
    //
    // Same shape as the index on FlatStorage, and deliberately so: open addressing on the `key_tail`
    // the caller already computed, positions rather than iterators, one pointer so this row grows by
    // eight rather than by a vector, and a copy leaves the index behind. Below the threshold nothing
    // changes and the vector the note describes is still what runs. A_K is append-only apart from
    // undo_warm_slot, which pops the back and drops the index rather than patching a probe run.
    static constexpr std::size_t index_from = 16;

    struct Index
    {
        std::vector<std::uint32_t> slot; // position + 1, 0 empty
        std::size_t mask;                // slot.size() - 1
    };

    std::unique_ptr<Index> aidx_{};

    void aidx_insert(std::size_t const pos)
    {
        std::size_t h =
            static_cast<std::size_t>(key_tail(accessed_storage_[pos])) &
            aidx_->mask;
        while (aidx_->slot[h] != 0) {
            h = (h + 1) & aidx_->mask;
        }
        aidx_->slot[h] = static_cast<std::uint32_t>(pos + 1);
    }

    void aidx_rebuild()
    {
        std::size_t cap = 32;
        while (cap < accessed_storage_.size() * 2) {
            cap *= 2;
        }
        if (!aidx_) {
            aidx_ = std::make_unique<Index>();
        }
        aidx_->slot.assign(cap, 0);
        aidx_->mask = cap - 1;
        for (std::size_t i = 0; i < accessed_storage_.size(); ++i) {
            aidx_insert(i);
        }
    }

    [[nodiscard]] bool
    aidx_has(bytes32_t const &key, std::uint64_t const tail) const
    {
        std::size_t h = static_cast<std::size_t>(tail) & aidx_->mask;
        for (;;) {
            std::uint32_t const p = aidx_->slot[h];
            if (p == 0) {
                return false;
            }
            if (key_equals(key, tail, accessed_storage_[p - 1])) {
                return true;
            }
            h = (h + 1) & aidx_->mask;
        }
    }
#endif

public:
    AccountSubstate() = default;
#ifdef MONAD_ZKVM_ZISK
    // The index is a cache derived from A_K, so a copy starts without one.
    AccountSubstate(AccountSubstate const &o)
        : destructed_(o.destructed_)
        , touched_(o.touched_)
        , accessed_(o.accessed_)
        , accessed_storage_(o.accessed_storage_)
    {
    }

    AccountSubstate &operator=(AccountSubstate const &o)
    {
        destructed_ = o.destructed_;
        touched_ = o.touched_;
        accessed_ = o.accessed_;
        accessed_storage_ = o.accessed_storage_;
        aidx_.reset();
        return *this;
    }

    AccountSubstate(AccountSubstate &&) noexcept = default;
    AccountSubstate &operator=(AccountSubstate &&) noexcept = default;
#else
    AccountSubstate(AccountSubstate &&) noexcept = default;
    AccountSubstate(AccountSubstate const &) = default;
    AccountSubstate &operator=(AccountSubstate &&) noexcept = default;
    AccountSubstate &operator=(AccountSubstate const &) = default;
#endif

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
        std::uint64_t const tail = key_tail(key);
#ifdef MONAD_ZKVM_ZISK
        if (aidx_) {
            if (aidx_has(key, tail)) {
                return EVMC_ACCESS_WARM;
            }
            accessed_storage_.push_back(key);
            if (aidx_->slot.size() < accessed_storage_.size() * 2) {
                aidx_rebuild();
            }
            else {
                aidx_insert(accessed_storage_.size() - 1);
            }
            return EVMC_ACCESS_COLD;
        }
#endif
        for (auto const &k : accessed_storage_) {
            if (key_equals(key, tail, k)) {
                return EVMC_ACCESS_WARM;
            }
        }
        accessed_storage_.push_back(key);
#ifdef MONAD_ZKVM_ZISK
        if (accessed_storage_.size() >= index_from) {
            aidx_rebuild();
        }
#endif
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
#ifdef MONAD_ZKVM_ZISK
        aidx_.reset();
#endif
    }
};

// 24 while A_K was an 8-byte persistent handle; a vector is 24 on its own. The number is here to
// catch growth nobody intended, so it moves with a change that was intended.
#ifdef MONAD_ZKVM_ZISK
static_assert(sizeof(AccountSubstate) == 40);
#else
static_assert(sizeof(AccountSubstate) == 32);
#endif

MONAD_NAMESPACE_END
