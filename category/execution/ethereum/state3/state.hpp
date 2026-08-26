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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/reserve_balance.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/reserve_balance.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <evmc/evmc.h>

#include <ankerl/unordered_dense.h>


#include <cstddef>
#include <cstdint>
#include <deque>
#include <span>
#include <vector>
#include <optional>

MONAD_NAMESPACE_BEGIN

class BlockState;

// A call frame's dirty-account list.
//
// MEASURED over 200 mainnet blocks (25815000-25815199): 2.25 accounts at the moment of insert
// (insert-weighted) and 2.54 by the time the frame closes, across 2,798 frames and 7,099 inserts
// per block. There is no tail to guard against -- weighting by insert LOWERS the mean, so the
// large frames one would worry about do not exist here.
//
// A hash set charged 189 steps per insert -- a 20-byte hash plus a probe -- to deduplicate two
// entries. A linear scan over the same two is a pair of 20-byte compares.
//
// Deduplication is NOT optional, and this is the whole reason the type is a set and not a vector:
// the undo log carries one record per listed address, so a repeated entry would journal the row
// twice and pop_reject would restore an intermediate value as if it were the pre-frame one.
class DirtyAccounts
{
    std::vector<Address> v_{};

public:
    // Returns whether the address was NEW to this frame. The caller needs that answer to know
    // whether to journal the row, and the scan that answers it is the same scan the insert
    // already does -- asking separately would walk the list twice.
    bool emplace(Address const &a)
    {
        for (auto const &x : v_) {
            if (__builtin_memcmp(x.bytes, a.bytes, sizeof(a.bytes)) == 0) {
                return false;
            }
        }
        v_.push_back(a);
        return true;
    }

    std::vector<Address>::const_iterator begin() const { return v_.begin(); }
    std::vector<Address>::const_iterator end() const { return v_.end(); }
    std::size_t size() const { return v_.size(); }
    bool empty() const { return v_.empty(); }
    std::span<Address const> span() const { return v_; }
};

class State
{
    template <typename K, typename V>
    using Map = ankerl::unordered_dense::segmented_map<K, V>;

    template <typename K>
    using Set = ankerl::unordered_dense::segmented_set<K>;

    BlockState &block_state_;

    Incarnation const incarnation_;

    Map<Address, OriginalAccountState> original_{};

    // One row per touched account, mutated in place. What used to be
    // VersionStack<AccountState> -- a deque of (version, AccountState) with copy-on-write per
    // frame -- is now a single row plus the undo log below.
    //
    // The version stack's copy was O(1) only because every container inside AccountState was
    // PERSISTENT: immer for storage, transient storage, the warm-slot set and the page map. That
    // is what made those containers unavoidable, and it is what cost 2.1 M steps a block in
    // per-access hashing and tree descent. A journal buys the same rollback without asking the
    // containers to be persistent.
    Map<Address, AccountState> current_{};

    // Undo log. A frame is a MARK, not a copy.
    //
    //   push()        remembers the log's length
    //   pop_reject()  replays the records above that mark, backwards
    //   pop_accept()  drops the mark, leaving the records to the parent frame
    //
    // One record per (frame, row): pushed exactly where the dirty-set insert reports the row as
    // new to this frame, which is the same once-per-frame-per-account rate the version stack
    // copied at. Duplicates across nested frames are harmless -- replayed backwards, the oldest
    // value lands last.
    //
    // Keyed by Address rather than by pointer: erase() moves a row, and a revert is rare enough
    // that a map lookup per record costs nothing next to being wrong.
    struct Undo
    {
        Address addr;
        // The row's value before this frame first changed it. Empty when the frame CREATED the
        // row: there is nothing to restore, so the record says erase, and an optional says that
        // rather than a 160-byte AccountState nobody reads.
        std::optional<AccountState> prev;
    };
    std::vector<Undo> undo_{};
    std::vector<size_t> undo_marks_{};

    // Logs are append-only within a transaction, and a rejected frame discards
    // exactly the ones it appended -- so a flat vector plus one watermark per
    // open version is the whole journal.
    //
    // This was VersionStack<immer::vector<Log>>. immer buys an O(1) snapshot
    // when a frame opens, which is real, but a watermark buys the same thing
    // for a size_t, and immer charges for it on every append: a node-path
    // allocation and an rbtree descent. Measured on block 25551991 -- 701
    // appends at 275.8 steps, 117,747 more inside immer's rbtree, and 103,679
    // in the deque of vectors that held the versions.
    std::vector<Receipt::Log> logs_{};
    // log_marks_.size() == version_: logs_.size() as it was when each open
    // frame started.
    std::vector<size_t> log_marks_{};

    Map<bytes32_t, vm::SharedVarcode> code_{};

    unsigned version_{0};

    std::deque<DirtyAccounts> dirty_;

    // One-entry memo for current_account_state(). Measured over 200 mainnet blocks
    // (25815000-25815199), 20,066 calls per block: 64.9% repeat the previous address, and 70.0% of
    // the dirty-set inserts it made were already present. Those two operations cost 2.65M and 2.43M
    // steps per block. Same shape as the single-entry sroot_ cache in PartialTrieDb.
    //
    // memo_val_ points into current_, whose segmented buckets do not move on insert; the ONE place
    // that can move an element is the erase loop in pop_reject(), which clears the memo.
    //
    // The epoch is what makes skipping the dirty-set insert safe, and version_ could not: frame
    // indices recur (push->1, pop->0, push->1), so a version_ stamp would skip an insert that the
    // second frame 1 genuinely needs. The epoch only ever increases.
    Address memo_addr_{};
    AccountState *memo_val_{nullptr};
    std::uint64_t memo_epoch_{0};
    std::uint64_t frame_epoch_{1};

    bool const relaxed_validation_{false};
    ReserveBalance rb_;

    template <Traits traits>
    friend bool revert_transaction_cached(State &);
    template <Traits traits>
        requires is_monad_trait_v<traits>
    friend void init_reserve_balance_context(
        State &, Address const &, Transaction const &,
        std::optional<uint256_t> const &, uint64_t, trace::StateTracer &,
        ChainContext<traits> const &);

public:
    OriginalAccountState &original_account_state(Address const &);

private:
    AccountState const &recent_account_state(Address const &);

    AccountState &current_account_state(Address const &);

    std::optional<Account> const &recent_account(Address const &);

    std::optional<Account> &current_account(Address const &);

public:
    State(BlockState &, Incarnation, bool relaxed_validation = false);

    State(State &&) = delete;
    State(State const &) = delete;
    State &operator=(State &&) = delete;
    State &operator=(State const &) = delete;

    Map<Address, OriginalAccountState> const &original() const;

    Map<Address, AccountState> const &current() const;

    Map<bytes32_t, vm::SharedVarcode> const &code() const;

    void push();

    void pop_accept();

    void pop_reject();

    // Return addresses marked dirty (including touched/accessed accounts) in
    // the currently pushed frame. Intended for observers that must inspect
    // frame-local metadata immediately before pop_accept() or pop_reject();
    // callers must not retain references beyond the frame pop.
    DirtyAccounts const &current_frame_dirty_accounts() const;

    // Records the row's pre-frame value so pop_reject can put it back. Called exactly where the
    // dirty-set insert reports the row as new to the frame.
    void journal_first_touch(
        Address const &address, AccountState const &row, bool created);

    ////////////////////////////////////////

    vm::VM &vm();

public:
    void set_original_nonce(Address const &, uint64_t nonce);

    ////////////////////////////////////////

    bool account_exists(Address const &);

    bool account_is_dead(Address const &);

    uint64_t get_nonce(Address const &);

    uint256_t get_balance(Address const &);

    uint256_t get_original_balance(Address const &);

    bytes32_t get_code_hash(Address const &);

    bool is_destructed(Address const &);

    bool is_current_incarnation(Address const &);

    bytes32_t get_storage(Address const &, bytes32_t const &key);

    bytes32_t get_transient_storage(Address const &, bytes32_t const &key);

    bool is_touched(Address const &);

    ////////////////////////////////////////

    void set_nonce(Address const &, uint64_t nonce);

    void add_to_balance(Address const &, uint256_t const &delta);

    void subtract_from_balance(Address const &, uint256_t const &delta);

    evmc_storage_status
    set_storage(Address const &, bytes32_t const &key, bytes32_t const &value);

    void set_transient_storage(
        Address const &, bytes32_t const &key, bytes32_t const &value);

    void touch(Address const &);

    evmc_access_status access_account(Address const &);

    template <Traits traits>
    evmc_access_status access_storage(Address const &, bytes32_t const &key);

    vm::Host::PageStorageStatus update_page(
        Address const &, bytes32_t const &key, evmc_storage_status status);

    ////////////////////////////////////////

    template <Traits traits>
    std::pair<bool, uint256_t>
    selfdestruct(Address const &, Address const &beneficiary);

    // YP (87)
    template <Traits traits>
    void destruct_suicides();

    // YP (88)
    void destruct_touched_dead();

    ////////////////////////////////////////

    vm::SharedVarcode read_code(bytes32_t const &code_hash);

    vm::SharedVarcode get_code(Address const &);

    size_t get_code_size(Address const &);

    size_t copy_code(
        Address const &, size_t offset, uint8_t *buffer, size_t buffer_size);

    void set_code(Address const &, byte_string_view code);

    ////////////////////////////////////////

    void create_contract(Address const &);

    /**
     * Creates an account that cannot be selfdestructed after Cancun.
     *
     * From Cancun onwards, only accounts created in the same transaction can be
     * selfdestructed. This method creates an account with a .tx incarnation
     * component that is guaranteed to be different from that of any actual
     * transaction; it will therefore never be selfdestructed.
     *
     * This is currently used to create authority accounts during EIP-7702
     * authority processing; changes to the state during that step are specified
     * to take place before any of the actual transactions in a block.
     */
    void create_account_no_rollback(Address const &);

    ////////////////////////////////////////

    std::vector<Receipt::Log> const &logs();

    void store_log(Receipt::Log const &);

    ////////////////////////////////////////

    void set_to_state_incarnation(Address const &);

    // RELAXED MERGE
    // if original and current can be adjusted to satisfy min balance, adjust
    // both values for merge
    bool try_fix_account_mismatch(
        Address const &, std::optional<Account> const &actual);

    /**
     * Checks whether the account currently has enough balance to cover `debit`
     * and records the relaxed-merge constraints needed for that debit.
     *
     * NOTE: This method mutates the account's OriginalAccountState by either
     * tightening the recorded `min_balance` or demanding exact balance
     * validation when the balance is insufficient. Callers should treat it as
     * a stateful helper rather than a pure predicate.
     */
    bool record_balance_constraint_for_debit(
        Address const &, uint256_t const &debit);
};

MONAD_NAMESPACE_END
