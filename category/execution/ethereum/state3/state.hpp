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
#include <optional>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

class BlockState;

// Per-frame dirty accounts, deduplicated by linear scan for typically small
// lists.
class DirtyAccounts
{
    std::vector<Address> addresses_{};

public:
    // Deduplicate entries for frame merging and reserve-balance tracking.
    // Returns true on insertion; current callers ignore the result.
    bool emplace(Address const &address)
    {
        for (auto const &existing_address : addresses_) {
            if (__builtin_memcmp(
                    existing_address.bytes,
                    address.bytes,
                    sizeof(address.bytes)) == 0) {
                return false;
            }
        }
        addresses_.push_back(address);
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
    // payload_index selects the old value in the matching payload vector.
    // Store addresses because erasing map entries can invalidate pointers.
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
            // undo_words_[payload_index]: appended warm-slot key.
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
    void journal_created(Address const &address);

    void journal_account(Address const &address, AccountState const &row);
    void
    journal_balance(Address const &address, uint256_t const &previous_state);
    void
    journal_code_hash(Address const &address, bytes32_t const &previous_state);
    void journal_nonce(Address const &address, std::uint64_t previous_state);
    void journal_flag(Address const &address, Undo::Kind kind);
    void journal_warm_slot(Address const &address, bytes32_t const &key);
    void journal_slot(
        Address const &address, bytes32_t const &key,
        bytes32_t const *previous_value);
    void journal_transient(
        Address const &address, AccountState const &row, bytes32_t const &key);
    void journal_pages(Address const &address, AccountState const &row);

    // True when a frame is open, i.e. when anything could still roll back.
    [[nodiscard]] bool journalling() const
    {
        return !undo_marks_.empty();
    }

    std::vector<Undo> undo_{};
    std::vector<std::optional<Account>> undo_accounts_{};
    std::vector<bytes32_t> undo_words_{};
    std::vector<std::uint64_t> undo_u64_{};
    std::vector<SlotUndo> undo_slots_{};
    std::vector<PageTracker> undo_pages_{};

    // Saved positions for each journal vector. ZisK uses byte offsets;
    // elsewhere only the account payload position is measured in bytes.
    struct UndoMark
    {
        size_t log;
        size_t accts;
        size_t words;
        size_t u64;
        size_t slots;
        size_t pages;
        // Power-of-two size for cheaper vector::size(), as in Undo.
#ifdef MONAD_ZKVM_ZISK
        // Padding is never read. Initialize only the six saved positions
        // to avoid zeroing the entire mark on every frame.
        size_t pad_[2];

        UndoMark(
            size_t const log_at, size_t const accts_at, size_t const words_at,
            size_t const u64_at, size_t const slots_at, size_t const pages_at)
            : log{log_at}
            , accts{accts_at}
            , words{words_at}
            , u64{u64_at}
            , slots{slots_at}
            , pages{pages_at}
        {
        }
#else
        size_t pad_[2]{};
#endif
    };

    static_assert(sizeof(UndoMark) == 64);

    std::vector<UndoMark> undo_marks_{};

    // Logs are append-only. Each frame saves the current size so reverting
    // can discard its logs without persistent-vector snapshots.
    std::vector<Receipt::Log> logs_{};
    // Saved log sizes in bytes; convert to counts only on rollback.
    // log_marks_.size() == version_.
    std::vector<size_t> log_marks_{};

    Map<bytes32_t, vm::SharedVarcode> code_{};

#if !defined(MONAD_ZKVM_VARCODE_CACHE)
    // Keep the code alive until the next borrowed lookup.
    vm::SharedVarcode borrowed_code_{};
#endif

    // Open frame count. Match vector sizes and avoid costly 32-bit accesses
    // on ZisK.
    size_t version_{0};

    std::deque<DirtyAccounts> dirty_;

    // Cache the last account lookup. Inserts preserve the pointer;
    // pop_reject clears it before erasing entries.
    //
    // An increasing epoch tracks dirty-set registration: version_ alone
    // cannot distinguish successive frames at the same depth.
    //
    // Align the address for the word loads used by ZisK comparisons.
    alignas(8) Address current_memo_address_{};
    AccountState *current_memo_state_{nullptr};
    std::uint64_t current_memo_epoch_{0};
    std::uint64_t frame_epoch_{1};

#ifdef MONAD_ZKVM_ZISK
    // Cache the last original-account lookup to avoid hashing its address
    // again. Segmented storage keeps pointers stable on insert; original_ never
    // erases.
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
    OriginalAccountState &original_account_state(Address const &);

private:
    // Reads may reuse the memo but never populate it: only the mutation path
    // registers dirty accounts and sets the corresponding epoch.
    [[nodiscard]] AccountState *cached_current_account(Address const &address)
    {
        if (current_memo_state_ != nullptr && __builtin_memcmp(
                                                  address.bytes,
                                                  current_memo_address_.bytes,
                                                  sizeof(address.bytes)) == 0) {
            return current_memo_state_;
        }
        return nullptr;
    }

    AccountState const &recent_account_state(Address const &);

    // Return the visible state and its original row without looking up
    // the original again when a current row already exists.
    struct AccountReadRows
    {
        AccountState const *visible;
        OriginalAccountState *original;
    };

    AccountReadRows rows_for_read(Address const &);

    AccountState &current_account_state(Address const &);

    // Whether SELFDESTRUCT to the account itself destroys the balance.
    template <Traits traits>
    bool selfdestruct_to_self_burns(Address const &);

    void zero_storage(Address const &, AccountState &);

    // Warm a slot in an already located account.
    template <Traits traits>
    monad_access_status
    access_storage_of(AccountState &, Address const &, bytes32_t const &key);

    // Read a slot from an account already located in current_.
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
#if defined(MONAD_ZKVM_ZISK)
    // Grow both mark vectors, then retry push with enough capacity.
    [[gnu::noinline, gnu::cold]] void push_after_growing();
#endif

    void pop_accept();

    void pop_reject();

    // Return addresses marked dirty (including touched/accessed accounts) in
    // the currently pushed frame. Intended for observers that must inspect
    // frame-local metadata immediately before pop_accept() or pop_reject();
    // callers must not retain references beyond the frame pop.
    DirtyAccounts const &current_frame_dirty_accounts() const;

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

    bytes32_t get_storage(Address const &address, bytes32_t const &key)
    {
        evmc_bytes32 value;
        get_storage_into(address, key, value);
        return bytes32_t{value};
    }

    // Write into the caller's buffer to avoid copies between word types.
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
    // Warm and read a slot with one account lookup; see vm::Host::sload_into.
    template <Traits traits>
    monad_access_status sload_into(
        Address const &, bytes32_t const &key, bool can_pay_cold_access,
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

    // Borrow the cached shared_ptr without changing its reference count.
    // Use it immediately: a later code lookup may replace the cached value.
    vm::SharedVarcode const &read_code_ref(bytes32_t const &code_hash);

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
