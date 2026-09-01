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

// Dirty-account tracking is unavailable in this guest configuration.
#if defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
class DirtyAccounts;
#else
// Per-frame dirty accounts, deduplicated by linear scan for small lists.
class DirtyAccounts
{
    std::vector<Address> v_{};

public:
    // Returns true on first insertion; no caller reads it. The scan is what
    // keeps the list free of duplicates, for pop_accept's merge and for the
    // reserve-balance hook.
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

    // Accounts are mutated in place and restored from the undo log on rollback.
    Map<Address, AccountState> current_{};

    // Save mutations in order; rejection replays backwards to the frame mark,
    // while acceptance keeps records for parent rollback. Repeated writes are
    // recorded separately, so the oldest value is restored last.
    //
    // All kinds share one log to preserve order (e.g. undo writes before
    // creation).
    // aux indexes the matching payload vector. Use addresses because map
    // erasure
    // can move entries.
    struct Undo
    {
        enum class Kind : unsigned char
        {
            // Erase the entry created in current_.
            Created,
            // undo_accts_[aux]: previous account_, including presence and
            // incarnation.
            AccountWhole,
            // undo_words_[aux]: previous balance, copied as raw bytes.
            Balance,
            // undo_words_[aux]
            CodeHash,
            // undo_u64_[aux]
            Nonce,
            // Recorded only on a false-to-true transition.
            FlagTouched,
            FlagDestructed,
            FlagAccessed,
            // undo_words_[aux]: appended warm-slot key.
            WarmSlot,
            // undo_slots_[aux]
            Slot,
            Transient,
            // undo_pages_[aux]: previous page-tracker handle.
            Pages,
        };

        Address addr;
        Kind kind;
        std::uint32_t aux;
    };

    struct SlotUndo
    {
        bytes32_t key;
        bytes32_t value;
        // If absent before the write, erase the slot on rollback; keeping it
        // would incorrectly include it in the commit set.
        bool had_value;
    };

    // Record a new current_ entry so rollback can erase it.
    void journal_created(Address const &address);

    void journal_account(Address const &address, AccountState const &row);
    void journal_balance(Address const &address, uint256_t const &prev);
    void journal_code_hash(Address const &address, bytes32_t const &prev);
    void journal_nonce(Address const &address, std::uint64_t prev);
    void journal_flag(Address const &address, Undo::Kind which);
    void journal_warm_slot(Address const &address, bytes32_t const &key);
    void journal_slot(
        Address const &address, bytes32_t const &key,
        bytes32_t const *prev);
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

    // Logs are append-only. Each frame saves the current size so reverting
    // can discard its logs without persistent-vector snapshots.
    std::vector<Receipt::Log> logs_{};
    // One saved size per open frame; log_marks_.size() == version_.
    std::vector<size_t> log_marks_{};

    Map<bytes32_t, vm::SharedVarcode> code_{};

    unsigned version_{0};

#if !defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    std::deque<DirtyAccounts> dirty_;
#endif

    // Cache the last account lookup. Inserts preserve the pointer;
    // pop_reject clears it before erasing entries.
    //
    // An increasing epoch tracks dirty-set registration: version_ alone
    // cannot distinguish successive frames at the same depth.
    //
    // alignas(8) because the key is READ as two 8-byte words and an Address
    // is 20 bytes: the pair of loads must not straddle a word boundary, which
    // ZisK charges 191 cells for against 16 for an aligned read. Holds the
    // property explicitly rather than leaving it to the layout of the members
    // above, which has already moved twice.
    alignas(8) Address memo_addr_{};
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
    // Reads may reuse the memo but never populate it: only the mutation path
    // registers dirty accounts and sets the corresponding epoch.
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

    // Resolve the visible account state and its original row with one address
    // lookup.
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
    DirtyAccounts const &current_frame_dirty_accounts() const;
#endif

    ////////////////////////////////////////

    vm::VM &vm();

public:
    void set_original_nonce(Address const &, uint64_t nonce);

    ////////////////////////////////////////

    bool account_exists(Address const &);

    bool account_is_dead(Address const &);

    bool account_has_code_or_nonce(Address const &);

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

    evmc_page_storage_status update_page(
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
