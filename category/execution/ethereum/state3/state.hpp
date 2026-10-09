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
#include <category/vm/evm/access_status.hpp>
#include <category/vm/evm/page_storage_status.hpp>
#include <category/vm/evm/storage_status.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <ankerl/unordered_dense.h>

#include <cstddef>
#include <cstdint>
#include <deque>
#include <optional>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

class BlockState;

#if defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
// This configuration omits dirty-account tracking.
class DirtyAccounts;
#else
// Per-frame dirty accounts, deduplicated by linear scan for small lists.
class DirtyAccounts
{
    std::vector<Address> addresses_{};

public:
    // Return true when adding an address not yet tracked in this frame.
    bool emplace(monad_address const &address)
    {
        for (auto const &existing_address : addresses_) {
            if (__builtin_memcmp(
                    existing_address.bytes,
                    address.bytes,
                    sizeof(address.bytes)) == 0) {
                return false;
            }
        }
        addresses_.emplace_back(address);
        return true;
    }

    std::vector<Address>::const_iterator begin() const
    {
        return addresses_.begin();
    }

    std::vector<Address>::const_iterator end() const
    {
        return addresses_.end();
    }

    std::size_t size() const
    {
        return addresses_.size();
    }

    bool empty() const
    {
        return addresses_.empty();
    }

    std::span<Address const> span() const
    {
        return addresses_;
    }
};

#endif

class State
{
    template <typename K, typename V>
    using Map = ankerl::unordered_dense::segmented_map<
        K, V, ankerl::unordered_dense::hash<K>,
        std::conditional_t<
            std::is_same_v<K, Address>, AddressEqual, std::equal_to<K>>>;

    template <typename K>
    using Set = ankerl::unordered_dense::segmented_set<K>;

    BlockState &block_state_;
#if defined(MONAD_ZKVM_ZISK)
    // Borrow the block's VM so vm() can return it directly from this header.
    vm::VM &vm_;
#endif

    Incarnation const incarnation_;

    Map<Address, OriginalAccountState> original_{};

    // Accounts are mutated in place and restored from the undo log on rollback.
    Map<Address, AccountState> current_{};

    // Replay mutations backward to the frame mark; acceptance retains them
    // for parent rollback. payload_index selects the previous-value vector.
    // Store addresses because erasing rows can invalidate pointers.
    //
    // Every append to a payload vector comes with its own record, whose
    // payload_index is the vector's size before the append: the guest's
    // pop_reject finds each vector's size at the frame mark in the
    // payload_index of the frame's earliest record of a kind that uses it.
    struct Undo
    {
        enum class Kind : unsigned char
        {
            // Erase the entry created in current_.
            Created,
            // undo_accounts_[payload_index]: previous account_, including
            // presence and incarnation.
            AccountWhole,
            // undo_words_[payload_index]: previous balance, copied as raw
            // bytes.
            Balance,
            // undo_words_[payload_index]
            CodeHash,
            // undo_u64_[payload_index]
            Nonce,
            // Recorded only on a false-to-true transition.
            FlagTouched,
            FlagDestructed,
            FlagAccessed,
            // undo_words_[payload_index]: appended warm-slot key. The guest
            // keeps no key, and its payload_index is 0: the key to remove is
            // the row's last.
            WarmSlot,
            // undo_slots_[payload_index]
            Slot,
            Transient,
            // undo_pages_[payload_index]: previous page-tracker handle.
            Pages,
        };

        Address address;
        Kind kind;
        // A full-width payload index avoids zero-extension and keeps Undo
        // at 32 bytes, so vector::size() can use a shift to count elements.
        std::uint64_t payload_index;

        Undo(
            monad_address const &address, Kind record_kind,
            std::uint64_t payload_position)
            : address{address}
            , kind{record_kind}
            , payload_index{payload_position}
        {
        }
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
        // Padding is never read; leave it uninitialized to avoid zeroing
        // the entire record before constructing its fields.
        unsigned char pad_[63];

        // vector::resize requires this even though we only use it to shrink.
        SlotUndo() = default;

        SlotUndo(
            bytes32_t const &slot_key, bytes32_t const &previous_value,
            bool const was_present)
            : key{slot_key}
            , value{previous_value}
            , had_value{was_present}
        {
        }
#else
        unsigned char pad_[63]{};
#endif
    };

    static_assert(sizeof(SlotUndo) == 128);

    // Record a new current_ entry so rollback can erase it.
    void journal_created(monad_address const &address);

    void journal_account(monad_address const &address, AccountState const &row);
    void journal_balance(
        monad_address const &address, uint256_t const &previous_value);
    void journal_code_hash(
        monad_address const &address, bytes32_t const &previous_value);
    void
    journal_nonce(monad_address const &address, std::uint64_t previous_value);
    void journal_flag(monad_address const &address, Undo::Kind kind);
#ifdef MONAD_ZKVM_ZISK
    void journal_warm_slot(monad_address const &address);
#else
    void journal_warm_slot(monad_address const &address, bytes32_t const &key);
#endif
    void journal_slot(
        monad_address const &address, bytes32_t const &key,
        bytes32_t const *previous_value);
    void journal_transient(
        monad_address const &address, AccountState const &row,
        bytes32_t const &key);
    void journal_pages(monad_address const &address, AccountState const &row);

    // True when a frame is open, i.e. when anything could still roll back.
    [[nodiscard]] bool journalling() const
    {
#if defined(MONAD_ZKVM_ZISK) && defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
        // One load where the vector test is two: push and both pops assert
        // undo_marks_.size() == version_, and no journal is written between
        // a pop's mark and its decrement.
        return version_ != 0;
#else
        return !undo_marks_.empty();
#endif
    }

    std::vector<Undo> undo_{};
    std::vector<std::optional<Account>> undo_accounts_{};
    std::vector<bytes32_t> undo_words_{};
    std::vector<std::uint64_t> undo_u64_{};
    std::vector<SlotUndo> undo_slots_{};
    std::vector<PageTracker> undo_pages_{};

#ifdef MONAD_ZKVM_ZISK
    // Save undo_ and logs_ byte offsets for each frame. Rollback recovers
    // payload-vector sizes from payload_index instead of saving them here.
    struct UndoMark
    {
        size_t undo_position;
        size_t log_position;

        // Built through a constructor, as SlotUndo is: an aggregate mark was
        // zeroed whole before its fields were written.
        UndoMark(size_t const undo_at, size_t const log_at)
            : undo_position{undo_at}
            , log_position{log_at}
        {
        }
    };

    static_assert(sizeof(UndoMark) == 16);
#else
    // Saved positions for each journal vector. Only the account payload
    // position is measured in bytes.
    struct UndoMark
    {
        size_t undo_position;
        size_t account_position;
        size_t word_position;
        size_t nonce_position;
        size_t slot_position;
        size_t page_position;
        // Power-of-two size for cheaper vector::size(), as in Undo.
        size_t pad_[2]{};
    };

    static_assert(sizeof(UndoMark) == 64);
#endif

    std::vector<UndoMark> undo_marks_{};

    // Append-only logs; frame marks let rollback discard the appended suffix.
    std::vector<Receipt::Log> logs_{};
#ifndef MONAD_ZKVM_ZISK
    // Saved log sizes in bytes; convert to counts only on rollback.
    // log_marks_.size() == version_. The guest keeps it in UndoMark.
    std::vector<size_t> log_marks_{};
#endif

    Map<bytes32_t, vm::SharedVarcode> code_{};

#if !defined(MONAD_ZKVM_VARCODE_CACHE)
    // Keep the code alive until the next borrowed lookup.
    vm::SharedVarcode borrowed_code_{};
#endif

    // Open frame count. Match vector sizes and avoid costly 32-bit accesses
    // on ZisK.
    size_t version_{0};

#if !defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    std::deque<DirtyAccounts> dirty_;
#endif

    // Inserts preserve this pointer; rollback clears it before erasing rows.
    // Align cached addresses for ZisK word comparisons.
    alignas(8) Address current_memo_address_{};
    AccountState *current_memo_state_{nullptr};
#if !defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    // A monotonic epoch tracks dirty registration across reused frame depths.
    std::uint64_t current_memo_epoch_{0};
    std::uint64_t frame_epoch_{1};
#endif

#ifdef MONAD_ZKVM_ZISK
    // Original rows are never erased; inserts preserve the cached pointer.
    alignas(8) Address original_memo_address_{};
    OriginalAccountState *original_memo_state_{nullptr};
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
    OriginalAccountState &original_account_state(monad_address const &);

private:
    // Reads may reuse the memo but never populate it: only the mutation path
    // registers dirty accounts and sets the corresponding epoch.
    [[nodiscard]] AccountState *
    cached_current_account(monad_address const &address)
    {
        if (current_memo_state_ != nullptr &&
            address_equal(address, current_memo_address_)) {
            return current_memo_state_;
        }
        return nullptr;
    }

    AccountState const &recent_account_state(monad_address const &);

    // Return the visible state and its original row without looking up
    // the original again when a current row already exists.
    struct AccountReadRows
    {
        AccountState const *visible;
        OriginalAccountState *original;
    };

    AccountReadRows rows_for_read(monad_address const &);

    AccountState &current_account_state(monad_address const &);

    // Whether SELFDESTRUCT to the account itself destroys the balance.
    template <Traits traits>
    bool selfdestruct_to_self_burns(monad_address const &);

    void zero_storage(monad_address const &, AccountState &);

    // Warm a slot in an already located account.
    template <Traits traits>
    AccessStatus access_storage_of(
        AccountState &, monad_address const &, bytes32_t const &key);

    // Read a slot from an account already located in current_.
    template <typename Output>
    [[gnu::always_inline]] inline void current_storage_into(
        AccountState const &, monad_address const &, bytes32_t const &key,
        Output &out);
#if defined(MONAD_ZKVM_ZISK)

    // Reuse the memo only when current_account_state needs no bookkeeping.
    [[nodiscard]] AccountState *
    cached_current_account_in_frame(monad_address const &address)
    {
    #if !defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
        if (current_memo_epoch_ != frame_epoch_) {
            return nullptr;
        }
    #endif
        return cached_current_account(address);
    }

    // Keep slow paths out of line. Account arguments come last to preserve
    // sload_into's argument registers when tail-calling these helpers.
    [[gnu::noinline]] AccessStatus sload_cold(
        monad_address const &, bytes32_t const &key, bool can_pay_cold_access,
        uint256_t &out, AccountState &);

    [[gnu::noinline]] AccessStatus sload_cold_uncached(
        monad_address const &, bytes32_t const &key, bool can_pay_cold_access,
        uint256_t &out, AccountState &);

    [[gnu::noinline]] AccessStatus sload_read(
        monad_address const &, bytes32_t const &key, uint256_t &out,
        OriginalAccountState &);

    template <Traits traits>
    [[gnu::noinline]] AccessStatus sload_full(
        monad_address const &, bytes32_t const &key, bool can_pay_cold_access,
        uint256_t &out);

    [[gnu::always_inline]] inline StorageStatus set_storage_of(
        AccountState &, monad_address const &, bytes32_t const &key,
        bytes32_t const &value);
    // Null pointers indicate values absent from the corresponding cache.
    [[gnu::always_inline]] inline StorageStatus set_storage_with_cached_values(
        AccountState &, monad_address const &, bytes32_t const &key,
        bytes32_t const &value, bytes32_t const *stored_value,
        bytes32_t const *cached_original_value);
#endif

    std::optional<Account> const &recent_account(monad_address const &);

    std::optional<Account> &current_account(monad_address const &);

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
#if defined(MONAD_ZKVM_ZISK)
    // Grow the mark vector, then retry push with enough capacity.
    [[gnu::noinline, gnu::cold]] void push_after_growing();
#endif

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
    void set_original_nonce(monad_address const &, uint64_t nonce);

    ////////////////////////////////////////

    bool account_exists(monad_address const &);

    bool account_is_dead(monad_address const &);

    bool account_has_code_or_nonce(monad_address const &);

    uint64_t get_nonce(monad_address const &);

    uint256_t get_balance(monad_address const &);

    uint256_t get_original_balance(monad_address const &);

    bytes32_t get_code_hash(monad_address const &);

#if defined(MONAD_ZKVM_ZISK)
    bool has_code(monad_address const &address)
    {
        auto const &account = recent_account(address);
        return account.has_value() && account->code_hash != NULL_HASH;
    }
#endif

    bool is_destructed(monad_address const &);

    bool is_current_incarnation(monad_address const &);

    bytes32_t get_storage(monad_address const &address, bytes32_t const &key)
    {
        bytes32_t value;
        get_storage_into(address, key, value);
        return bytes32_t{value};
    }

    // Write into the caller's buffer to avoid copies between word types.
    void get_storage_into(
        monad_address const &, bytes32_t const &key, bytes32_t &out);

    bytes32_t
    get_transient_storage(monad_address const &, bytes32_t const &key);

    bool is_touched(monad_address const &);

    ////////////////////////////////////////

    void set_nonce(monad_address const &, uint64_t nonce);

    void add_to_balance(monad_address const &, uint256_t const &delta);

    void subtract_from_balance(monad_address const &, uint256_t const &delta);

    StorageStatus set_storage(
        monad_address const &, bytes32_t const &key, bytes32_t const &value);

    void set_transient_storage(
        monad_address const &, bytes32_t const &key, bytes32_t const &value);

    void touch(monad_address const &);

    AccessStatus access_account(monad_address const &);

    template <Traits traits>
    AccessStatus access_storage(monad_address const &, bytes32_t const &key);

#if defined(MONAD_ZKVM_ZISK)
    // Warm and read a slot with one account lookup; see vm::Host::sload_into.
    template <Traits traits>
    AccessStatus sload_into(
        monad_address const &, bytes32_t const &key, bool can_pay_cold_access,
        uint256_t &out);

    template <Traits traits>
    vm::runtime::SstoreStatus sstore_into(
        monad_address const &, bytes32_t const &key, bytes32_t const &value,
        bool can_pay_cold_access);
#endif

    PageStorageStatus update_page(
        monad_address const &, bytes32_t const &key, StorageStatus status);

    ////////////////////////////////////////

    template <Traits traits>
    std::pair<bool, uint256_t>
    selfdestruct(monad_address const &, monad_address const &beneficiary);

    // YP (87)
    template <Traits traits>
    void destruct_suicides();

    // YP (88)
    void destruct_touched_dead();

    ////////////////////////////////////////

    vm::SharedVarcode read_code(bytes32_t const &code_hash);

    // Borrow the cached shared_ptr without changing its reference count.
    // Use it immediately: a later code lookup may replace the cached value.
    vm::SharedVarcode const &read_code_ref(bytes32_t const &code_hash);

    vm::SharedVarcode get_code(monad_address const &);

    size_t get_code_size(monad_address const &);

    size_t copy_code(
        monad_address const &, size_t offset, uint8_t *buffer,
        size_t buffer_size);

#if defined(MONAD_ZKVM_ZISK) && defined(MONAD_ZKVM_VARCODE_CACHE)
    struct AccountCode
    {
        bytes32_t const &hash;
        // Null when the account does not exist.
        vm::SharedVarcode const *code;
    };

    AccountCode account_code(monad_address const &);
#endif

#if defined(MONAD_ZKVM_ZISK)
    // Read the EIP-7702 delegation target directly from cached code.
    std::optional<Address> delegate_of(monad_address const &);
#endif

    void set_code(monad_address const &, byte_string_view code);

    ////////////////////////////////////////

    void create_contract(monad_address const &);

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
    void create_account_no_rollback(monad_address const &);

    ////////////////////////////////////////

    std::vector<Receipt::Log> const &logs();
    // Transfer the logs to the receipt after all frames have closed.
    // Later event processing reads them from the receipt.
    std::vector<Receipt::Log> take_logs();

    void store_log(Receipt::Log const &);
    void store_log(Receipt::Log &&);
#if defined(MONAD_ZKVM_ZISK)
    // Convert maker directly into the new log; no intermediate Log to move.
    template <typename Maker>
    Receipt::Log const &emplace_log(Maker const &maker)
    {
        return logs_.emplace_back(maker);
    }
#endif

    ////////////////////////////////////////

    void set_to_state_incarnation(monad_address const &);

    // RELAXED MERGE
    // if original and current can be adjusted to satisfy min balance, adjust
    // both values for merge
    bool try_fix_account_mismatch(
        monad_address const &, std::optional<Account> const &actual);

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
        monad_address const &, uint256_t const &debit);
};

MONAD_NAMESPACE_END
