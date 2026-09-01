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
// Deduplication is not optional WHILE THE LIST IS READ: a repeated entry would be handed to
// pop_accept's merge twice. It has nothing to do with the undo log any more -- that carries typed
// records keyed by row and replays backwards on its own, which is why pop_reject moves this list out
// and never looks at it. The claim three lines up that pop_reject depends on the deduplication was
// left behind by the change that introduced typed records; it is not true today.
//
// Under MONAD_ZKVM_NO_DIRTY_ACCOUNTS the list is write-only and compiles away. What reads it:
// pop_accept, to hand the addresses to the PARENT's copy of the same list -- self-referential, so it
// disappears with the list -- and State::current_frame_dirty_accounts, whose only caller is
// trace/state_tracer.cpp, which zkvm/guest/CMakeLists.txt excludes from the guest. Neither the
// accessor nor StateTracer has a symbol in the shipped ELF. pop_reject DOES read it, through
// rb_.on_pop_reject(accounts.span()) -- an earlier version of this comment said it read nothing --
// but under the flag that span is empty, so the call stands and does nothing.
//
// The flag is declared only in the guest's CMakeLists, so the host keeps the list and its tracer.
#if defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)

class DirtyAccounts
{
    static constexpr Address const *nothing_ = nullptr;

public:
    // Kept: emplace's return value said whether the address was new to the frame, and nothing has
    // read that since typed records replaced the row snapshot.
    bool emplace(Address const &) { return true; }

    Address const *begin() const { return nothing_; }
    Address const *end() const { return nothing_; }
    std::size_t size() const { return 0; }
    bool empty() const { return true; }
    std::span<Address const> span() const { return {}; }
};

#else

class DirtyAccounts
{
    std::vector<Address> v_{};

public:
    // Returns whether the address was NEW to this frame. Nothing reads that any more -- it used to
    // drive the row snapshot, which typed records replaced -- so the scan now only keeps the list
    // free of duplicates for pop_accept's merge and for the reserve-balance hook.
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

#endif

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
    // A journal, not a version stack. Rollback used to require every container on a row to be
    // PERSISTENT -- and persistence cost 2.1 M steps a block in per-access hashing and tree
    // descent. The journal buys the same rollback without asking anything of the containers, so
    // the row's slots, transient slots and warm-slot set are all flat now. Only the page map is
    // still immer.
    Map<Address, AccountState> current_{};

    // Undo log. A frame is a MARK, not a copy.
    //
    //   push()        remembers the log's length
    //   pop_reject()  replays the records above that mark, backwards
    //   pop_accept()  drops the mark, leaving the records to the parent frame
    //
    // A record covers ONE mutation, and carries only what that mutation overwrote. The row-wide
    // snapshot it replaces cost 201 steps per first touch (1.43 M a block, measured) to copy 184
    // bytes plus two vector allocations, most of which the frame never went on to change.
    //
    // ONE log for every kind, with payloads in side vectors that `aux` indexes. One log and not one
    // per kind because the order BETWEEN kinds is load-bearing: a row created and then written must
    // have its slots and fields restored before the row is erased, and a single backwards replay is
    // what guarantees that.
    //
    // Every real mutation is journalled -- not the frame's first change of each field. Deduplicating
    // would need per-field state per frame, and nested frames make that subtle; duplicates are
    // already correct, because replayed backwards the oldest value lands last. If the entry volume
    // ever costs more than the copying it saved, the profile will say so.
    //
    // Keyed by Address rather than by pointer: erase() moves a row, and a revert is rare enough that
    // a map lookup per record costs nothing next to being wrong.
    struct Undo
    {
        enum class Kind : unsigned char
        {
            // The frame CREATED the row. Nothing to restore, so the record says erase.
            Created,
            // undo_accts_[aux]: account_ as it was. For the transitions the narrow kinds below
            // cannot express -- appearing, being cleared, a new incarnation -- all of them rare.
            AccountWhole,
            // undo_words_[aux]: the raw bytes of the previous balance. Stored and restored verbatim,
            // never interpreted, so no endian conversion is involved.
            Balance,
            // undo_words_[aux]
            CodeHash,
            // undo_u64_[aux]
            Nonce,
            // The flag was false. Pushed only on a real transition, so a second touch() in the same
            // frame adds nothing.
            FlagTouched,
            FlagDestructed,
            FlagAccessed,
            // undo_words_[aux]: the warm-slot key that was appended. Replaces copying the whole
            // A_K vector: a frame warms a few of the keys a row holds.
            WarmSlot,
            // undo_slots_[aux]
            Slot,
            Transient,
            // undo_pages_[aux]: the page map's handle. Unreachable on the Ethereum traits
            // (mip_8_active() is false there), so this is correctness for the Monad traits at no
            // cost here.
            Pages,
        };

        Address addr;
        Kind kind;
        std::uint32_t aux;
#ifdef MONAD_ZKVM_KECCAK_SITES
        // Diagnostic: left behind by a frame that was ACCEPTED, so replaying it means a parent
        // revert is undoing work an accepted child did -- the nested combination a mainnet corpus
        // exercises only by accident.
        bool promoted{false};
#endif
    };

    struct SlotUndo
    {
        bytes32_t key;
        bytes32_t value;
        // False when the slot was absent. Restoring then means removing it again, not writing the
        // pre-state value back: BlockState commits every slot the overlay lists, so a slot left
        // behind by a reverted write would join the commit set.
        bool had_value;
    };

    // Pushed where the dirty-set insert reports the row as new to the frame, and now ONLY for a row
    // the frame created: an existing row needs no snapshot, because each mutation journals itself.
    void journal_created(Address const &address);

    void journal_account(Address const &address, AccountState const &row);
    void journal_balance(Address const &address, uint256_t const &prev);
    void journal_code_hash(Address const &address, bytes32_t const &prev);
    void journal_nonce(Address const &address, std::uint64_t prev);
    void journal_flag(Address const &address, Undo::Kind which);
    void journal_warm_slot(Address const &address, bytes32_t const &key);
    void journal_slot(
        Address const &address, AccountState const &row, bytes32_t const &key);
    void journal_transient(
        Address const &address, AccountState const &row, bytes32_t const &key);
    void journal_pages(Address const &address, AccountState const &row);

    // True when a frame is open, i.e. when anything could still roll back.
    [[nodiscard]] bool journalling() const
    {
        return !undo_marks_.empty();
    }

    std::vector<Undo> undo_{};
    std::vector<std::optional<Account>> undo_accts_{};
    std::vector<bytes32_t> undo_words_{};
    std::vector<std::uint64_t> undo_u64_{};
    std::vector<SlotUndo> undo_slots_{};
    std::vector<PageTracker> undo_pages_{};

    // Each open frame's watermark in all six vectors.
    struct UndoMark
    {
        size_t log;
        size_t accts;
        size_t words;
        size_t u64;
        size_t slots;
        size_t pages;
    };

    std::vector<UndoMark> undo_marks_{};

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

#if defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    // No container at all. DirtyAccounts is empty under this flag (above), so a
    // stack of them holds nothing -- and the only two facts the code ever read
    // from the stack are its depth and whether it is empty, which version_
    // already carries. The asserts that pinned dirty_.size() to version_ are
    // what say so. Every operation below is therefore exactly a no-op here, and
    // what disappears with them is a deque's chunk map and index arithmetic on
    // 20,433 account lookups and 3,028 frame pushes a block.
    static void dirty_mark(Address const &) {}

    static void dirty_push() {}

    static DirtyAccounts dirty_take()
    {
        return {};
    }

    static void dirty_promote_to_parent() {}
#else
    std::deque<DirtyAccounts> dirty_;

    void dirty_mark(Address const &address)
    {
        if (!dirty_.empty()) {
            MONAD_GUEST_SITE(DIRTY_EMPLACE);
            dirty_.back().emplace(address);
        }
    }

    void dirty_push()
    {
        dirty_.emplace_back();
    }

    DirtyAccounts dirty_take()
    {
        auto accounts = std::move(dirty_.back());
        dirty_.pop_back();
        return accounts;
    }

    // Accepted: the parent's list gains what this frame touched.
    void dirty_promote_to_parent()
    {
        auto const accounts = std::move(dirty_.back());
        dirty_.pop_back();
        for (auto const &address : accounts) {
            if (!dirty_.empty()) {
                dirty_.back().emplace(address);
            }
        }
    }
#endif

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
    // The one-entry memo, for reads: answer from it, never replace it. A read does no dirty
    // insert, so populating it would have to leave memo_epoch_ at a value frame_epoch_ can never
    // take -- and it would evict the entry current_account_state is about to want. It also would
    // not buy anything: measured over five blocks, get_storage names the memoised address 99.9 %
    // of the time and recent_account_state 87.3 %, both against a memo only the mutation path
    // fills. What populating here could add is the rounding.
    [[nodiscard]] AccountState *memoised(Address const &address)
    {
        if (memo_val_ != nullptr &&
            __builtin_memcmp(
                address.bytes, memo_addr_.bytes, sizeof(address.bytes)) == 0) {
            return memo_val_;
        }
        return nullptr;
    }

    AccountState const &recent_account_state(Address const &);

    // The row a read should see, and the original row behind it, resolved in ONE address lookup.
    // Callers needing both used to ask twice -- and three times when there was no current row,
    // because recent_account_state goes to original_ itself and the caller then asked again.
    struct RowPair
    {
        AccountState const *recent;
        OriginalAccountState *orig;
    };

    RowPair rows_for_read(Address const &);

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
#if !defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    // Guarded rather than stubbed: its only caller is trace/state_tracer.cpp,
    // which the guest's CMakeLists excludes, so a reference from the guest
    // should fail the build and not return an empty answer.
    DirtyAccounts const &current_frame_dirty_accounts() const;
#endif

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
    void store_log(Receipt::Log &&);

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
