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

#include <bit>
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/state3/account_substate.hpp>
#include <category/execution/ethereum/state3/page_tracker.hpp>

#include <evmc/evmc.h>

#include <cstdint>
#include <optional>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

class State;
class BlockState;

namespace trace
{
    struct PrestateTracer;
    struct StateDiffTracer;
}

// The slots a row holds. This was immer::map. A persistent map bought an O(1) copy of the row when
// a frame opened; the undo log does not need that copy -- it journals the slots a frame actually
// WRITES, and a frame writes two of the thirty a row holds.
//
// Unsorted, and deliberately: insertion appends, so it never moves an existing entry and an index
// into this vector stays valid. Sorting it would memmove the tail on every insert to save a handful
// of 32-byte compares. Same reasoning, and the same measurement, that put a vector under A_K.
class FlatStorage
{
    std::vector<std::pair<bytes32_t, bytes32_t>> v_{};

#ifdef MONAD_ZKVM_ZISK
    // A scan is O(row), and a row is small until it is not. Measured over 200 mainnet blocks: on a
    // median block the scan visits about one entry a call and the vector is exactly right, but the
    // corpus is bimodal -- 27 of the 200 blocks cost more than 5 % above a competing guest, and on
    // the worst of them get_storage, access_storage and set_storage run 3.0 M scan iterations
    // against a median block's 63,760, 15.2 % of the block's steps against 1.6 %. That is the whole
    // of the tail: the shape of the deficit is identical on both blocks, only its scale differs.
    //
    // So keep the vector, and index it only once a row is big enough for the scan to lose. Open
    // addressing on the `key_tail` the callers already compute -- a keccak-derived slot key needs no
    // further mixing, and a small-integer key carries its value in the same tail -- so a probe is a
    // mask, a load and a compare. Positions and not iterators, because a position survives the
    // append that the comment above relies on; `erase` is the one operation that moves an entry, and
    // it drops the index rather than patching it, being rare.
    // The gate a lookup pays is a null test on that pointer -- not
    // `v_.size() < index_from`, which is a pointer subtraction at 60 cells and a compare at 60 on
    // every find of every row, indexed or not. Measured: that test alone cost +0.08 % on a median
    // block, as much as the whole tail gain is worth there. Crossing the threshold is decided in
    // upsert, which runs a third as often and already knows the size it just changed.
    // One pointer and not two members, because every row pays the footprint and only a big row uses
    // it: AccountState is size-asserted, the undo log allocates one per frame per account, and two
    // FlatStorage members double whatever is added. A null pointer is the gate and an absent index.
    static constexpr std::size_t index_from = 16;

    struct Index
    {
        std::vector<std::uint32_t> slot; // position + 1, 0 empty
        std::size_t mask;                // slot.size() - 1
        unsigned shift;                  // 64 - log2(slot.size())
    };

    mutable std::unique_ptr<Index> idx_{};

    void insert_index(std::size_t const pos) const
    {
        std::size_t h =
            static_cast<std::size_t>(key_tail(v_[pos].first) >> idx_->shift);
        while (idx_->slot[h] != 0) {
            h = (h + 1) & idx_->mask;
        }
        idx_->slot[h] = static_cast<std::uint32_t>(pos + 1);
    }

    void rebuild_index() const
    {
        std::size_t cap = 32;
        while (cap < v_.size() * 2) {
            cap *= 2;
        }
        if (!idx_) {
            idx_ = std::make_unique<Index>();
        }
        idx_->slot.assign(cap, 0);
        idx_->mask = cap - 1;
        idx_->shift = 64u - static_cast<unsigned>(std::bit_width(cap) - 1);
        for (std::size_t i = 0; i < v_.size(); ++i) {
            insert_index(i);
        }
    }

    [[nodiscard]] std::uint32_t
    lookup(bytes32_t const &key, std::uint64_t const tail) const
    {
        std::size_t h = static_cast<std::size_t>(tail >> idx_->shift);
        for (;;) {
            std::uint32_t const p = idx_->slot[h];
            if (p == 0) {
                return 0;
            }
            if (key_equals(key, tail, v_[p - 1].first)) {
                return p;
            }
            h = (h + 1) & idx_->mask;
        }
    }

    void drop_index()
    {
        idx_.reset();
    }
#endif

public:
#ifdef MONAD_ZKVM_ZISK
    // The index is a cache derived from v_, so a copy does not carry it: the row the undo log takes
    // per frame per account starts unindexed and builds one only if it is used enough to want one.
    // Copying it instead would copy a table the copy may never probe.
    FlatStorage() = default;
    FlatStorage(FlatStorage const &o)
        : v_(o.v_)
    {
    }
    FlatStorage &operator=(FlatStorage const &o)
    {
        v_ = o.v_;
        idx_.reset();
        return *this;
    }
    FlatStorage(FlatStorage &&) = default;
    FlatStorage &operator=(FlatStorage &&) = default;
#endif

    [[nodiscard]] bytes32_t const *find(bytes32_t const &key) const
    {
        std::uint64_t const tail = key_tail(key);
#ifdef MONAD_ZKVM_ZISK
        if (idx_) {
            std::uint32_t const p = lookup(key, tail);
            return p ? &v_[p - 1].second : nullptr;
        }
#endif
        for (auto const &e : v_) {
            if (key_equals(key, tail, e.first)) {
                return &e.second;
            }
        }
        return nullptr;
    }

    void upsert(bytes32_t const &key, bytes32_t const &value)
    {
        std::uint64_t const tail = key_tail(key);
#ifdef MONAD_ZKVM_ZISK
        if (idx_) {
            if (std::uint32_t const p = lookup(key, tail); p != 0) {
                v_[p - 1].second = value;
                return;
            }
            v_.emplace_back(key, value);
            if (idx_->slot.size() < v_.size() * 2) {
                rebuild_index();
            }
            else {
                insert_index(v_.size() - 1);
            }
            return;
        }
#endif
        for (auto &e : v_) {
            if (key_equals(key, tail, e.first)) {
                e.second = value;
                return;
            }
        }
        // Floored on the first insert. This is the path that takes it: the
        // indexed one above only runs once idx_ exists, by which point the
        // capacity is past the floor. A container that starts empty pays every
        // doubling in full here -- operator delete is a no-op and the
        // allocator never reuses a block -- and most touched accounts hold a
        // handful of slots, so a floor is cheaper than sizing at construction
        // for the accounts that hold none.
        if (MONAD_UNLIKELY(v_.capacity() == 0)) {
            v_.reserve(8);
        }
        v_.emplace_back(key, value);
#ifdef MONAD_ZKVM_ZISK
        if (v_.size() >= index_from) {
            rebuild_index();
        }
#endif
    }

    // Removing a slot restores "absent", which is not the same as present-and-equal-to-pre-state:
    // BlockState commits every slot the overlay lists, so a slot left behind by a reverted write
    // would join the commit set.
    void erase(bytes32_t const &key)
    {
        std::uint64_t const tail = key_tail(key);
        for (auto &e : v_) {
            if (key_equals(key, tail, e.first)) {
                e = v_.back();
                v_.pop_back();
#ifdef MONAD_ZKVM_ZISK
                drop_index();
#endif
                return;
            }
        }
    }

    [[nodiscard]] bool empty() const
    {
        return v_.empty();
    }

    [[nodiscard]] std::size_t size() const
    {
        return v_.size();
    }

    [[nodiscard]] auto begin() const
    {
        return v_.begin();
    }

    [[nodiscard]] auto end() const
    {
        return v_.end();
    }
};

class OriginalAccountState;

class AccountState : public AccountSubstate
{
public: // TODO
    using StorageMap = FlatStorage;

protected:
    std::optional<Account> account_{};

private:
    friend class State;
    friend class BlockState;

    friend std::optional<Account> const &
    get_account_for_trace(AccountState const &as)
    {
        return as.account_;
    }

public:
    StorageMap storage_{};
    StorageMap transient_storage_{};
    PageTracker page_tracker_{};

    // The row in original_ this one was created from, or null on an original row. A storage read
    // that misses the overlay needs the pre-state row, and finding it by address hashed the same
    // 20 bytes a second time: get_storage runs 5,184 times a block at 187 steps, and two of those
    // lookups are the same lookup.
    //
    // Safe to hold because original_ is a segmented map that is only ever inserted into -- one
    // try_emplace, no erase, no clear -- so an element never moves for the life of the block.
    // current_ IS erased, in pop_reject, but that erases the row holding the pointer, not its
    // target.
    OriginalAccountState *orig_{nullptr};

    evmc_storage_status zero_out_key(
        bytes32_t const &key, bytes32_t const &original_value,
        bytes32_t const &current_value);

    evmc_storage_status set_current_value(
        bytes32_t const &key, bytes32_t const &value,
        bytes32_t const &original_value, bytes32_t const &current_value);

public:
    explicit AccountState(std::optional<Account> &&account)
        : account_{std::move(account)}
    {
    }

    explicit AccountState(std::optional<Account> const &account)
        : account_{account}
    {
    }

    AccountState(AccountState &&) noexcept = default;
    AccountState(AccountState const &) = default;
    AccountState &operator=(AccountState &&) noexcept = default;
    AccountState &operator=(AccountState const &) = default;

    [[nodiscard]] bool has_account() const
    {
        return account_.has_value();
    }

    [[nodiscard]] bytes32_t get_code_hash() const
    {
        if (MONAD_LIKELY(account_.has_value())) {
            return account_->code_hash;
        }
        return NULL_HASH;
    }

    [[nodiscard]] uint64_t get_nonce() const
    {
        if (MONAD_LIKELY(account_.has_value())) {
            return account_->nonce;
        }
        return 0;
    }

    [[nodiscard]] std::optional<Incarnation> get_incarnation() const
    {
        if (MONAD_LIKELY(account_.has_value())) {
            return account_->incarnation;
        }
        return std::nullopt;
    }

    bytes32_t get_transient_storage(bytes32_t const &key) const
    {
        if (auto const *const it = transient_storage_.find(key);
            MONAD_LIKELY(it)) {
            return *it;
        }
        return {};
    }

    // `prev` is the caller's probe of this slot -- null when absent -- so this
    // does not repeat it.
    evmc_storage_status set_storage(
        bytes32_t const &key, bytes32_t const &value,
        bytes32_t const &original_value, bytes32_t const *const prev)
    {
        bytes32_t const current_value = prev ? *prev : original_value;
        if (value == bytes32_t{}) {
            return zero_out_key(key, original_value, current_value);
        }
        return set_current_value(key, value, original_value, current_value);
    }

    void set_transient_storage(bytes32_t const &key, bytes32_t const &value)
    {
        transient_storage_.upsert(key, value);
    }
};

// Kept exact so unintended growth fails the build. The undo log copies this row once per frame per
// account -- everything but its storage_, which is journalled per slot -- so its size is a cost, not
// a detail.
//
// 16 wider than the two persistent handles it replaced, not 32: the second vector lands in padding
// the row already carried, so the number is not the arithmetic and has to be read off the compiler.
#ifdef MONAD_ZKVM_ZISK
// 216 in the guest: each of the two FlatStorage members carries one pointer to its slot index, and
// AccountSubstate one more for A_K's. The
// row's storage_ is journalled per slot rather than copied, so the growth is footprint and not copy
// time, and it buys the tail described on FlatStorage -- 3.0 M scan iterations on the worst of 200
// blocks against 63,760 on a median one.
static_assert(sizeof(AccountState) == 216);
#else
static_assert(sizeof(AccountState) == 192);
#endif

// RELAXED MERGE
// track the min original balance needed at start of transaction and if the
// original and current balances can be adjusted
// The ORIGINAL row's slot cache: pre-state values the block has read. Monotone by construction --
// inserted once per slot on first read, never overwritten, and never rolled back, because
// original_ sits outside revert semantics entirely (find and try_emplace are the only operations
// on it, and set_original_nonce / set_min_balance are deliberately not journalled). That is what
// lets it flatten with NO journal at all, ahead of the current overlay which needs one.
//
// Unsorted with a linear scan, not sorted: insertion is append-only and never moves an existing
// entry, so an index into it stays valid -- which is what the row work above this will want. A
// sorted vector would memmove ~1 kB per insert to save a handful of compares.
class PrestateStorage
{
    std::vector<std::pair<bytes32_t, bytes32_t>> v_{};

#ifdef MONAD_ZKVM_ZISK
    // The third of these, and the one the other two leave behind: State::get_storage probes the
    // current overlay first and falls through to here for every slot the block has read but not
    // written, which on a storage-heavy contract is most of them. After the overlay and A_K were
    // indexed, get_storage was still 4.92 % of the worst block's steps against 0.77 % of a median
    // one -- this scan is what remained.
    //
    // The simplest of the three: append-only with no erase at all, so the index is never dropped
    // and insert never has to look for what it is adding. Otherwise the same -- open addressing on
    // the `key_tail` the caller already computed, positions rather than iterators, one pointer, and
    // a copy leaves it behind. Below the threshold the scan the comment above describes is what
    // runs, unchanged.
    static constexpr std::size_t index_from = 16;

    struct Index
    {
        std::vector<std::uint32_t> slot; // position + 1, 0 empty
        std::size_t mask;                // slot.size() - 1
        unsigned shift;                  // 64 - log2(slot.size())
    };

    std::unique_ptr<Index> idx_{};

    void idx_insert(std::size_t const pos)
    {
        // The home bucket is the HIGH bits, not `tail & mask`. key_tail reads bytes 24..31 with a
        // native-endian load and bytes32_t is big-endian, so a small-integer slot key -- the most
        // common shape there is -- puts its value in the high bytes of that word and leaves the low
        // bits zero. Masking the low bits sends every such key to bucket 0 and the probe degenerates
        // into the scan it replaced, with the index's cost on top: measured on block 25552422,
        // 560,346 probe steps and +3.7 % on the block. A keccak-derived key is uniform either way.
        std::size_t h = static_cast<std::size_t>(
            key_tail(v_[pos].first) >> idx_->shift);
        while (idx_->slot[h] != 0) {
            h = (h + 1) & idx_->mask;
        }
        idx_->slot[h] = static_cast<std::uint32_t>(pos + 1);
    }

    void idx_rebuild()
    {
        std::size_t cap = 32;
        while (cap < v_.size() * 2) {
            cap *= 2;
        }
        if (!idx_) {
            idx_ = std::make_unique<Index>();
        }
        idx_->slot.assign(cap, 0);
        idx_->mask = cap - 1;
        idx_->shift = 64u - static_cast<unsigned>(std::bit_width(cap) - 1);
        for (std::size_t i = 0; i < v_.size(); ++i) {
            idx_insert(i);
        }
    }
#endif

public:
#ifdef MONAD_ZKVM_ZISK
    // The index is a cache derived from v_, so a copy starts without one.
    PrestateStorage() = default;

    PrestateStorage(PrestateStorage const &o)
        : v_(o.v_)
    {
    }

    PrestateStorage &operator=(PrestateStorage const &o)
    {
        v_ = o.v_;
        idx_.reset();
        return *this;
    }

    PrestateStorage(PrestateStorage &&) = default;
    PrestateStorage &operator=(PrestateStorage &&) = default;
#endif

    bytes32_t const *find(bytes32_t const &k) const
    {
        std::uint64_t const tail = key_tail(k);
#ifdef MONAD_ZKVM_ZISK
        if (idx_) {
            std::size_t h = static_cast<std::size_t>(tail >> idx_->shift);
            for (;;) {
                std::uint32_t const p = idx_->slot[h];
                if (p == 0) {
                    return nullptr;
                }
                if (key_equals(k, tail, v_[p - 1].first)) {
                    return &v_[p - 1].second;
                }
                h = (h + 1) & idx_->mask;
            }
        }
#endif
        for (auto const &e : v_) {
            if (key_equals(k, tail, e.first)) {
                return &e.second;
            }
        }
        return nullptr;
    }

    void insert(bytes32_t const &k, bytes32_t const &v)
    {
        if (MONAD_UNLIKELY(v_.capacity() == 0)) {
            v_.reserve(8);
        }
        v_.emplace_back(k, v);
#ifdef MONAD_ZKVM_ZISK
        if (idx_) {
            if (idx_->slot.size() < v_.size() * 2) {
                idx_rebuild();
            }
            else {
                idx_insert(v_.size() - 1);
            }
        }
        else if (v_.size() >= index_from) {
            idx_rebuild();
        }
#endif
    }

    bool empty() const { return v_.empty(); }
    std::size_t size() const { return v_.size(); }
    auto begin() const { return v_.begin(); }
    auto end() const { return v_.end(); }
};

class OriginalAccountState final : public AccountState
{
    bool validate_exact_balance_{false};
    uint256_t min_balance_{0};

public:
    // The base's storage_ is unused for an original row: this replaces it. Both are flat vectors
    // now, so the two could be one member -- what keeps them apart is the contract. This one is
    // append-only and never overwrites, which is why it needs no journal; the base's is a mutable
    // overlay with erase(). Merging them would hand an original row operations it must never use.
    PrestateStorage prestate_storage_{};

    explicit OriginalAccountState(std::optional<Account> &&account)
        : AccountState(std::move(account))
    {
    }

    explicit OriginalAccountState(std::optional<Account> const &account)
        : AccountState{account}
    {
    }

    [[nodiscard]] bool validate_exact_balance() const
    {
        return validate_exact_balance_;
    }

    [[nodiscard]] uint256_t const &min_balance() const
    {
        return min_balance_;
    }

    void set_validate_exact_balance()
    {
        validate_exact_balance_ = true;
    }

    uint256_t get_balance_pessimistic()
    {
        set_validate_exact_balance();
        if (account_.has_value()) {
            return account_->balance;
        }
        return 0;
    }

private:
    friend class State;

    void set_min_balance(uint256_t const &value)
    {
        MONAD_ASSERT(account_.has_value());
        MONAD_ASSERT(account_->balance >= value);
        if (value > min_balance_) {
            min_balance_ = value;
        }
    }
};

MONAD_NAMESPACE_END
