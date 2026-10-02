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
#include <category/vm/evm/access_status.h>
#include <category/vm/evm/page_storage_status.h>
#include <category/vm/evm/storage_status.h>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

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
#if defined(MONAD_ZKVM_ZISK)
    // The block's VM, kept here so vm() is inline: a message call asked
    // another translation unit for it.
    vm::VM &vm_;
#endif

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
        // A full-width payload index avoids zero-extension and keeps Undo
        // at 32 bytes, so vector::size() uses a shift instead of a multiply.
        std::uint64_t aux;
    };

    static_assert(sizeof(Undo) == 32);

    struct SlotUndo
    {
        bytes32_t key;
        bytes32_t value;
        // If absent before the write, erase the slot on rollback; keeping it
        // would incorrectly include it in the commit set.
        bool had_value;
        // Power-of-two size for cheaper vector::size(), as in Undo.
#ifdef MONAD_ZKVM_ZISK
        // Left as it is: built as an aggregate, the record was zeroed whole,
        // a 128-byte memset before its fields were written.
        unsigned char pad_[63];

        // For resize's truncation, which never builds one.
        SlotUndo() = default;

        SlotUndo(bytes32_t const &k, bytes32_t const &v, bool const had)
            : key{k}
            , value{v}
            , had_value{had}
        {
        }
#else
        unsigned char pad_[63]{};
#endif
    };

    static_assert(sizeof(SlotUndo) == 128);

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

    // Each open frame's watermark in all six vectors. `accts` is in bytes:
    // an optional<Account> is 88 of them, and a count would cost a multiply
    // by 11's inverse on every frame, where only a rejection needs it.
    struct UndoMark
    {
        size_t log;
        size_t accts;
        size_t words;
        size_t u64;
        size_t slots;
        size_t pages;
        // Power-of-two size for cheaper vector::size(), as in Undo.
        size_t pad_[2]{};
    };

    static_assert(sizeof(UndoMark) == 64);

    std::vector<UndoMark> undo_marks_{};

    // Logs are append-only. Each frame saves the current size so reverting
    // can discard its logs without persistent-vector snapshots.
    std::vector<Receipt::Log> logs_{};
    // One saved size per open frame, in bytes as UndoMark::accts (a Log is
    // 80); log_marks_.size() == version_.
    std::vector<size_t> log_marks_{};

    Map<bytes32_t, vm::SharedVarcode> code_{};

    // The last code read from the block, by hash: a call reads its callee's
    // code twice in a row, to test it for an EIP-7702 delegation and then to
    // run it, and the block's code for a hash does not change.
    bytes32_t last_code_hash_{};
#if defined(MONAD_ZKVM_VARCODE_CACHE)
    // Where the VM's cache keeps it: a copy would raise and lower its count.
    vm::SharedVarcode const *last_code_{nullptr};
#else
    vm::SharedVarcode last_code_{};
#endif

    // The number of open frames. A size_t, as the vector sizes every push and
    // pop compares it with: an unsigned is loaded sign-extended, widened with
    // two shifts for the compare, and stored in four bytes, which ZisK prices
    // as an unaligned access.
    size_t version_{0};

#if !defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    std::deque<DirtyAccounts> dirty_;
#endif

    // Cache the last account lookup. Inserts preserve the pointer;
    // pop_reject clears it before erasing entries.
    //
    // alignas(8) because the key is READ as two 8-byte words and an Address
    // is 20 bytes: the pair of loads must not straddle a word boundary, which
    // ZisK charges 191 cells for against 16 for an aligned read. Holds the
    // property explicitly rather than leaving it to the layout of the members
    // above, which has already moved twice.
    alignas(8) Address memo_addr_{};
    AccountState *memo_val_{nullptr};
#if !defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    // An increasing epoch tracks dirty-set registration: version_ alone
    // cannot distinguish successive frames at the same depth.
    std::uint64_t memo_epoch_{0};
    std::uint64_t frame_epoch_{1};
#endif

#ifdef MONAD_ZKVM_ZISK
    // The same for original_account_state: original_ never erases, so its
    // rows never move. A transaction's sender is looked up there several
    // times running.
    alignas(8) Address orig_memo_addr_{};
    OriginalAccountState *orig_memo_{nullptr};
#endif

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
        if (memo_val_ != nullptr && address == memo_addr_) {
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

    // access_storage's work on the account it looked up.
    template <Traits traits>
    monad_access_status
    access_storage_of(AccountState &, Address const &, bytes32_t const &key);

    // get_storage_into's work on an account in current_.
    [[gnu::always_inline]] inline void current_storage_into(
        AccountState const &, Address const &, bytes32_t const &key,
        evmc_bytes32 &out);

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

#if defined(MONAD_ZKVM_ZISK)
    vm::VM &vm()
    {
        return vm_;
    }
#else
    vm::VM &vm();
#endif

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

#if defined(MONAD_ZKVM_ZISK)
    // get_code_hash's hash where the account keeps it: a returned copy is
    // 32 bytes written through the caller's stack.
    bytes32_t const &code_hash_ref(Address const &);
#endif

    bool is_destructed(Address const &);

    bool is_current_incarnation(Address const &);

    bytes32_t get_storage(Address const &address, bytes32_t const &key)
    {
        bytes32_t value;
        get_storage_into(address, key, value);
        return value;
    }

    // Writes the value where the caller wants it: a caller that hands it on
    // as another word type would otherwise copy it once more.
    void
    get_storage_into(Address const &, bytes32_t const &key, evmc_bytes32 &out);

    bytes32_t get_transient_storage(Address const &, bytes32_t const &key);

    bool is_touched(Address const &);

    ////////////////////////////////////////

    void set_nonce(Address const &, uint64_t nonce);

    void add_to_balance(Address const &, uint256_t const &delta);

    void subtract_from_balance(Address const &, uint256_t const &delta);

    monad_storage_status
    set_storage(Address const &, bytes32_t const &key, bytes32_t const &value);

    void set_transient_storage(
        Address const &, bytes32_t const &key, bytes32_t const &value);

    void touch(Address const &);

    monad_access_status access_account(Address const &);

    template <Traits traits>
    monad_access_status access_storage(Address const &, bytes32_t const &key);

#if defined(MONAD_ZKVM_ZISK)
    // SLOAD's access_storage and get_storage_into, with one lookup of the
    // account: see vm::Host::sload_into.
    template <Traits traits>
    monad_access_status sload_into(
        Address const &, bytes32_t const &key, bool read_cold,
        evmc_bytes32 &out);
#endif

    monad_page_storage_status update_page(
        Address const &, bytes32_t const &key, monad_storage_status status);

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

    // read_code's varcode where it is kept, for a caller done with the
    // reference before the next read_code: a copy increments the use count
    // and its release decrements it, each a 4-byte load and store.
    vm::SharedVarcode const &read_code_ref(bytes32_t const &code_hash);

    vm::SharedVarcode get_code(Address const &);

    size_t get_code_size(Address const &);

    size_t copy_code(
        Address const &, size_t offset, uint8_t *buffer, size_t buffer_size);

#if defined(MONAD_ZKVM_ZISK)
    // EIP-7702's delegate of the address, read where its code is kept, and
    // returned where it lies in the code, or null.
    Address const *delegate_of(Address const &);
#endif

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
    // The logs, handed over and cleared. A receipt is their last reader: the
    // events that follow read the receipt's, and nothing reverts afterwards.
    std::vector<Receipt::Log> take_logs();

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
