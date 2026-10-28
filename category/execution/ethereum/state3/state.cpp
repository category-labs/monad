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

#include <category/execution/ethereum/state3/state.hpp>
#include <category/vm/evm/access_status.hpp>
#include <category/vm/evm/page_storage_status.hpp>
#include <category/vm/evm/storage_status.hpp>

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/vm/code.hpp>
#if defined(MONAD_ZKVM_ZISK)
    #include <category/vm/evm/delegation.hpp>
#endif
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <immer/map_transient.hpp>
#include <immer/vector.hpp>

#include <cstddef>
#include <cstdint>
#include <limits>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace
{
    // Measure used bytes without dividing by sizeof(T).
    template <typename T>
    [[gnu::always_inline]] inline size_t bytes_of(std::vector<T> const &values)
    {
        return static_cast<size_t>(
            reinterpret_cast<char const *>(std::to_address(values.cend())) -
            reinterpret_cast<char const *>(values.data()));
    }
}

#ifdef MONAD_ZKVM_ZISK
OriginalAccountState::OriginalAccountState(StateDelta &delta)
    : AccountState{delta.account.second}
    , block_delta_{&delta}
{
}
#endif

OriginalAccountState &
State::original_account_state(monad_address const &address)
{
#ifdef MONAD_ZKVM_ZISK
    if (original_memo_state_ != nullptr &&
        address_equal(address, original_memo_address_)) {
        return *original_memo_state_;
    }

    // Pass a recipe, not the result of read_account_delta: function arguments
    // are evaluated before try_emplace, even when the row already exists.
    // This avoids both an unnecessary block lookup and a separate find here.
    struct DeferredAccountDelta
    {
        BlockState &block_state;
        monad_address const &address;

        // If the row is missing, try_emplace constructs OriginalAccountState.
        // Its constructor needs StateDelta&, so C++ invokes this conversion.
        // An existing row requires no construction and never calls this code.
        operator StateDelta &() const
        {
            return block_state.read_account_delta(address);
        }
    };

    // DeferredAccountDelta is temporary; the delta belongs to BlockState.
    // The new row retains a pointer to that stable delta, not to the temporary.
    OriginalAccountState &row =
        original_
            .try_emplace(address, DeferredAccountDelta{block_state_, address})
            .first->second;
    static_cast<monad_address &>(original_memo_address_) = address;
    original_memo_state_ = &row;
    return row;
#else
    auto it = original_.find(address);
    if (it == original_.end()) {
        // block state
        auto const account = block_state_.read_account(address);
        it = original_.try_emplace(address, account).first;
    }
    return it->second;
#endif
}

AccountState const &State::recent_account_state(monad_address const &address)
{
    if (AccountState *const cached = cached_current_account(address);
        cached != nullptr) {
        return *cached;
    }
    // current
    auto const it = current_.find(address);
    if (it != current_.end()) {
        return it->second;
    }
    // original
    return original_account_state(address);
}

AccountState &State::current_account_state(monad_address const &address)
{
    // Reuse the cached account. When dirty tracking is enabled, register
    // it again if the frame epoch changed.
    if (current_memo_state_ != nullptr &&
        address_equal(address, current_memo_address_)) {
#if !defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
        if (current_memo_epoch_ != frame_epoch_) {
            if (!dirty_.empty()) {
                // Track the account only; each mutation records its own undo
                // state.
                dirty_.back().emplace(address);
            }
            current_memo_epoch_ = frame_epoch_;
        }
#endif
        return *current_memo_state_;
    }

    // current
    auto it = current_.find(address);
    bool created = false;
    if (MONAD_UNLIKELY(it == current_.end())) {
        // original
        auto &account_state = original_account_state(address);
#if defined(MONAD_ZKVM_ZISK)
        // Only account_ is populated in the original's AccountState base.
        // Construct empty containers directly; original slots stay in
        // prestate_storage_ and remain accessible through original_state_.
        it = current_.try_emplace(address, account_state.account_).first;
#else
        it = current_.try_emplace(address, account_state).first;
#endif
        it->second.original_state_ = &account_state;
#if defined(MONAD_ZKVM_ZISK)
        // EIP-3651 warmth is transaction-wide, so do not journal this access.
        if (defers_beneficiary_ && address == block_state_.beneficiary()) {
            (void)it->second.access();
            beneficiary_row_created_ = true;
        }
#endif
        created = true;
        // Record creation separately from dirty tracking.
        journal_created(address);
    }
#if !defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    if (!dirty_.empty()) {
        dirty_.back().emplace(address);
    }
#endif
    (void)created;
    static_cast<monad_address &>(current_memo_address_) = address;
    current_memo_state_ = &it->second;
#if !defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    current_memo_epoch_ = frame_epoch_;
#endif
    return it->second;
}

// Save each mutation separately. Outside a frame, no undo record is needed.
void State::journal_created(monad_address const &address)
{
    if (!journalling()) {
        return;
    }
    undo_.emplace_back(address, Undo::Kind::Created, 0);
}

void State::journal_account(
    monad_address const &address, AccountState const &row)
{
    if (!journalling()) {
        return;
    }
    undo_.emplace_back(
        address, Undo::Kind::AccountWhole, undo_accounts_.size());
    undo_accounts_.push_back(row.account_);
}

void State::journal_balance(
    monad_address const &address, uint256_t const &previous_value)
{
    if (!journalling()) {
        return;
    }
    bytes32_t balance_bytes;
    // Save and restore the balance as raw bytes, without numeric conversion.
    static_assert(sizeof(balance_bytes.bytes) == sizeof(previous_value));
    __builtin_memcpy(
        balance_bytes.bytes, &previous_value, sizeof(balance_bytes.bytes));
    undo_.emplace_back(address, Undo::Kind::Balance, undo_words_.size());
    undo_words_.push_back(balance_bytes);
}

void State::journal_code_hash(
    monad_address const &address, bytes32_t const &previous_value)
{
    if (!journalling()) {
        return;
    }
    undo_.emplace_back(address, Undo::Kind::CodeHash, undo_words_.size());
    undo_words_.push_back(previous_value);
}

void State::journal_nonce(
    monad_address const &address, std::uint64_t const previous_value)
{
    if (!journalling()) {
        return;
    }
    undo_.emplace_back(address, Undo::Kind::Nonce, undo_u64_.size());
    undo_u64_.push_back(previous_value);
}

void State::journal_flag(monad_address const &address, Undo::Kind const kind)
{
    if (!journalling()) {
        return;
    }
    undo_.emplace_back(address, kind, 0);
}

#ifdef MONAD_ZKVM_ZISK
// No key and no payload: the row's last warm slot is the one to remove (see
// AccountSubstate::undo_warm_slot), and a constant payload_index keeps the
// record from reading undo_words_'s size.
void State::journal_warm_slot(monad_address const &address)
{
    if (!journalling()) {
        return;
    }
    undo_.emplace_back(address, Undo::Kind::WarmSlot, 0);
}
#else
void State::journal_warm_slot(
    monad_address const &address, bytes32_t const &key)
{
    if (!journalling()) {
        return;
    }
    undo_.emplace_back(address, Undo::Kind::WarmSlot, undo_words_.size());
    undo_words_.push_back(key);
}
#endif

// Reuse the caller's lookup to save the old value without another probe.
void State::journal_slot(
    monad_address const &address, bytes32_t const &key,
    bytes32_t const *const previous_value)
{
    if (!journalling()) {
        return;
    }
    undo_.emplace_back(address, Undo::Kind::Slot, undo_slots_.size());
#ifdef MONAD_ZKVM_ZISK
    // Both branches refer to existing objects, avoiding a temporary value.
    static constexpr bytes32_t zero{};
    undo_slots_.emplace_back(
        key,
        previous_value ? *previous_value : zero,
        previous_value != nullptr);
#else
    undo_slots_.emplace_back(
        key,
        previous_value ? *previous_value : bytes32_t{},
        previous_value != nullptr);
#endif
}

void State::journal_transient(
    monad_address const &address, AccountState const &row, bytes32_t const &key)
{
    if (!journalling()) {
        return;
    }
    bytes32_t const *const previous_value = row.transient_storage_.find(key);
    undo_.emplace_back(address, Undo::Kind::Transient, undo_slots_.size());
#ifdef MONAD_ZKVM_ZISK
    // Borrow the prior value or a static zero, as in journal_slot.
    static constexpr bytes32_t zero{};
    undo_slots_.emplace_back(
        key,
        previous_value ? *previous_value : zero,
        previous_value != nullptr);
#else
    undo_slots_.emplace_back(
        key,
        previous_value ? *previous_value : bytes32_t{},
        previous_value != nullptr);
#endif
}

void State::journal_pages(monad_address const &address, AccountState const &row)
{
    if (!journalling()) {
        return;
    }
    undo_.emplace_back(address, Undo::Kind::Pages, undo_pages_.size());
    undo_pages_.push_back(row.page_tracker_);
}

std::optional<Account> &State::current_account(monad_address const &address)
{
    return current_account_state(address).account_;
}

State::State(
    BlockState &block_state, Incarnation const incarnation,
    bool const relaxed_validation)
    : block_state_{block_state}
#if defined(MONAD_ZKVM_ZISK)
    , vm_{block_state.vm()}
#endif
    , incarnation_{incarnation}
    , relaxed_validation_{relaxed_validation}
    , rb_{this}
{
    // Reserve initial capacity to avoid repeated growth for each transaction.
    // The guest's bump allocator does not reclaim old allocations.
    // Containers can still grow beyond this floor.
    constexpr size_t INITIAL_CAPACITY = 16;
    original_.reserve(INITIAL_CAPACITY);
    current_.reserve(INITIAL_CAPACITY);
#ifdef MONAD_ZKVM_ZISK
    // Reserve more room for slot-related undo records to avoid early growth
    // and copies. reserve() allocates capacity without constructing entries.
    // Keep the existing balance-payload capacity after removing warm-slot keys.
    constexpr size_t INITIAL_SLOT_CAPACITY = 64;
    undo_.reserve(INITIAL_SLOT_CAPACITY);
    undo_accounts_.reserve(INITIAL_CAPACITY);
    undo_words_.reserve(INITIAL_SLOT_CAPACITY);
    undo_u64_.reserve(INITIAL_CAPACITY);
    undo_slots_.reserve(INITIAL_SLOT_CAPACITY);
#else
    undo_.reserve(INITIAL_CAPACITY);
    undo_accounts_.reserve(INITIAL_CAPACITY);
    undo_words_.reserve(INITIAL_CAPACITY);
    undo_u64_.reserve(INITIAL_CAPACITY);
    undo_slots_.reserve(INITIAL_CAPACITY);
#endif
    undo_marks_.reserve(INITIAL_CAPACITY);
    logs_.reserve(INITIAL_CAPACITY);
#ifndef MONAD_ZKVM_ZISK
    log_marks_.reserve(INITIAL_CAPACITY);
#endif
}

State::Map<Address, OriginalAccountState> const &State::original() const
{
    return original_;
}

State::Map<Address, AccountState> const &State::current() const
{
    return current_;
}

State::Map<bytes32_t, vm::SharedVarcode> const &State::code() const
{
    return code_;
}

#if !defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
DirtyAccounts const &State::current_frame_dirty_accounts() const
{
    MONAD_ASSERT(version_);
    MONAD_ASSERT(dirty_.size() == version_);

    return dirty_.back();
}
#endif

#if defined(MONAD_ZKVM_ZISK)
void State::push_after_growing()
{
    undo_marks_.reserve(2 * undo_marks_.capacity() + 1);
    push();
}
#endif

void State::push()
{
#if defined(MONAD_ZKVM_ZISK)
    // Keep growth calls and their register saves out of the usual push path.
    if (MONAD_UNLIKELY(undo_marks_.size() == undo_marks_.capacity())) {
        return push_after_growing();
    }
#endif
#if !defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    MONAD_ASSERT(dirty_.size() == version_);
#else
    MONAD_ASSERT(undo_marks_.size() == version_);
    MONAD_ASSERT(
        !rb_.tracking_enabled(), "reserve tracking requires dirty accounts");
#endif

#if !defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    ++frame_epoch_;
#endif

    ++version_;
#if !defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    dirty_.emplace_back();
#endif
    // Construct the frame mark in place.
#if defined(MONAD_ZKVM_ZISK)
    // Save byte offsets without computing element counts on every push.
    // Rollback recovers payload sizes from the undo records (see UndoMark).
    undo_marks_.emplace_back(bytes_of(undo_), bytes_of(logs_));
#else
    undo_marks_.emplace_back(
        undo_.size(),
        bytes_of(undo_accounts_),
        undo_words_.size(),
        undo_u64_.size(),
        undo_slots_.size(),
        undo_pages_.size());
    log_marks_.push_back(bytes_of(logs_));
#endif
}

void State::pop_accept()
{
    MONAD_ASSERT(version_);
#if !defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    MONAD_ASSERT(dirty_.size() == version_);
#else
    MONAD_ASSERT(undo_marks_.size() == version_);
    MONAD_ASSERT(
        !rb_.tracking_enabled(), "reserve tracking requires dirty accounts");
#endif

#if !defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    ++frame_epoch_;

    auto const accounts = std::move(dirty_.back());
    dirty_.pop_back();
    // Keep changes and merge dirty accounts into the parent. Retain undo
    // records so a later parent rejection can roll back the accepted changes.
    for (auto const &dirty_address : accounts) {
        if (!dirty_.empty()) {
            dirty_.back().emplace(dirty_address);
        }
    }
#endif
    undo_marks_.pop_back();
    // No open frame can roll back these records; release them.
    if (undo_marks_.empty()) {
        undo_.clear();
        undo_accounts_.clear();
        undo_words_.clear();
        undo_u64_.clear();
        undo_slots_.clear();
        undo_pages_.clear();
    }

    // Accepted: the frame's logs stay where they are, only its watermark goes,
    // which the guest keeps in its UndoMark.
#if !defined(MONAD_ZKVM_ZISK)
    log_marks_.pop_back();
#endif

    --version_;
}

void State::pop_reject()
{
    MONAD_ASSERT(version_);
#if !defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    MONAD_ASSERT(dirty_.size() == version_);
#else
    MONAD_ASSERT(undo_marks_.size() == version_);
    MONAD_ASSERT(
        !rb_.tracking_enabled(), "reserve tracking requires dirty accounts");
#endif

#if !defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    ++frame_epoch_;

    auto const accounts = std::move(dirty_.back());
    dirty_.pop_back();
#endif

    // Rejected: drop exactly what this frame appended.
#if defined(MONAD_ZKVM_ZISK)
    logs_.resize(undo_marks_.back().log_position / sizeof(Receipt::Log));
#else
    logs_.resize(log_marks_.back() / sizeof(Receipt::Log));
    log_marks_.pop_back();
#endif

    // Rollback may erase and move map entries, invalidating the cached
    // pointer.
    current_memo_state_ = nullptr;

    // Replay backwards to restore the earliest values last.
    UndoMark const mark = undo_marks_.back();
    undo_marks_.pop_back();
#if defined(MONAD_ZKVM_ZISK)
    // Each payload vector's size at the mark: the payload_index of the frame's
    // earliest record that appended to it, which the backward replay meets
    // last. A vector's records index its entries in order: an accepted inner
    // frame left its records in place, and a rejected one removed them with
    // their entries. A vector the frame did not append to keeps its size.
    size_t account_payload_count = undo_accounts_.size();
    size_t word_payload_count = undo_words_.size();
    size_t nonce_payload_count = undo_u64_.size();
    size_t slot_payload_count = undo_slots_.size();
    size_t page_payload_count = undo_pages_.size();
    while (bytes_of(undo_) > mark.undo_position) {
#else
    while (undo_.size() > mark.undo_position) {
#endif
        Undo &undo_record = undo_.back();
        if (undo_record.kind == Undo::Kind::Created) {
            current_.erase(undo_record.address);
            undo_.pop_back();
            continue;
        }
        // Creation precedes mutations, so reverse replay restores the fields
        // before erasing their entry.
        auto const it = current_.find(undo_record.address);
        MONAD_ASSERT(it != current_.end());
        AccountState &row = it->second;
        switch (undo_record.kind) {
        case Undo::Kind::Created:
            break; // handled above

        case Undo::Kind::AccountWhole:
            row.account_ = std::move(undo_accounts_[undo_record.payload_index]);
#if defined(MONAD_ZKVM_ZISK)
            account_payload_count = undo_record.payload_index;
#endif
            break;

        case Undo::Kind::Balance:
            // Account-clearing cleanup runs outside frames; the account still
            // exists.
            MONAD_ASSERT(row.account_.has_value());
            __builtin_memcpy(
                &row.account_->balance,
                undo_words_[undo_record.payload_index].bytes,
                sizeof(undo_words_[undo_record.payload_index].bytes));
#if defined(MONAD_ZKVM_ZISK)
            word_payload_count = undo_record.payload_index;
#endif
            break;

        case Undo::Kind::CodeHash:
            MONAD_ASSERT(row.account_.has_value());
            row.account_->code_hash = undo_words_[undo_record.payload_index];
#if defined(MONAD_ZKVM_ZISK)
            word_payload_count = undo_record.payload_index;
#endif
            break;

        case Undo::Kind::Nonce:
            MONAD_ASSERT(row.account_.has_value());
            row.account_->nonce = undo_u64_[undo_record.payload_index];
#if defined(MONAD_ZKVM_ZISK)
            nonce_payload_count = undo_record.payload_index;
#endif
            break;

        case Undo::Kind::FlagTouched:
            row.undo_touched();
            break;

        case Undo::Kind::FlagDestructed:
            row.undo_destructed();
            break;

        case Undo::Kind::FlagAccessed:
            row.undo_accessed();
            break;

        case Undo::Kind::WarmSlot:
#if defined(MONAD_ZKVM_ZISK)
            // No payload: see journal_warm_slot.
            row.undo_warm_slot();
            // Original values survive rollback; their warmth does not.
            row.original_state_->cached_slots_may_be_cold_ = 1;
#else
            row.undo_warm_slot(undo_words_[undo_record.payload_index]);
#endif
            break;

        case Undo::Kind::Slot: {
            SlotUndo const &slot_undo = undo_slots_[undo_record.payload_index];
            if (slot_undo.had_value) {
                row.storage_.upsert(slot_undo.key, slot_undo.value);
            }
            else {
                row.storage_.erase(slot_undo.key);
            }
#if defined(MONAD_ZKVM_ZISK)
            slot_payload_count = undo_record.payload_index;
#endif
            break;
        }

        case Undo::Kind::Transient: {
            SlotUndo const &slot_undo = undo_slots_[undo_record.payload_index];
            if (slot_undo.had_value) {
                row.transient_storage_.upsert(slot_undo.key, slot_undo.value);
            }
            else {
                row.transient_storage_.erase(slot_undo.key);
            }
#if defined(MONAD_ZKVM_ZISK)
            slot_payload_count = undo_record.payload_index;
#endif
            break;
        }

        case Undo::Kind::Pages:
            row.page_tracker_ =
                std::move(undo_pages_[undo_record.payload_index]);
#if defined(MONAD_ZKVM_ZISK)
            page_payload_count = undo_record.payload_index;
#endif
            break;
        }
        undo_.pop_back();
    }
#if defined(MONAD_ZKVM_ZISK)
    undo_accounts_.resize(account_payload_count);
    undo_words_.resize(word_payload_count);
    undo_u64_.resize(nonce_payload_count);
    undo_slots_.resize(slot_payload_count);
    undo_pages_.resize(page_payload_count);
#else
    undo_accounts_.resize(
        mark.account_position / sizeof(std::optional<Account>));
    undo_words_.resize(mark.word_position);
    undo_u64_.resize(mark.nonce_position);
    undo_slots_.resize(mark.slot_position);
    undo_pages_.resize(mark.page_position);
#endif
    if (undo_marks_.empty()) {
        undo_.clear();
        undo_accounts_.clear();
        undo_words_.clear();
        undo_u64_.clear();
        undo_slots_.clear();
        undo_pages_.clear();
    }

#if !defined(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    rb_.on_pop_reject(accounts.span());
#endif

    --version_;
}

#if !defined(MONAD_ZKVM_ZISK)
vm::VM &State::vm()
{
    return block_state_.vm();
}
#endif

State::AccountReadRows State::rows_for_read(monad_address const &address)
{
    auto const it = current_.find(address);
    if (it != current_.end()) {
        MONAD_ASSERT(it->second.original_state_ != nullptr);
        return {&it->second, it->second.original_state_};
    }
    // Without a current row, reads see the original state.
    auto &original = original_account_state(address);
    return {&original, &original};
}

std::optional<Account> const &
State::recent_account(monad_address const &address)
{
    return recent_account_state(address).account_;
}

void State::set_original_nonce(
    monad_address const &address, uint64_t const nonce)
{
    auto &account_state = original_account_state(address);
    auto &account = account_state.account_;
    if (!account.has_value()) {
        account = Account{};
    }
    account->nonce = nonce;
}

bool State::account_exists(monad_address const &address)
{
    return recent_account(address).has_value();
}

bool State::account_is_dead(monad_address const &address)
{
    return is_dead(recent_account(address));
}

bool State::account_has_code_or_nonce(monad_address const &address)
{
    auto const &account = recent_account(address);
    if (!account.has_value()) {
        return false;
    }

    auto const &account_val = account.value();
    return account_val.nonce > 0 || account_val.code_hash != NULL_HASH;
}

uint64_t State::get_nonce(monad_address const &address)
{
    auto const &account = recent_account(address);
    if (MONAD_LIKELY(account.has_value())) {
        return account.value().nonce;
    }
    return 0;
}

uint256_t State::get_balance(monad_address const &address)
{
#if defined(MONAD_ZKVM_NO_MERGE_CONSTRAINTS)
    // Sequential execution needs no merge constraint or original-row lookup.
    auto const &account = recent_account(address);
#else
    auto const [visible, original] = rows_for_read(address);
    original->set_validate_exact_balance();
    auto const &account = visible->account_;
#endif
    if (MONAD_LIKELY(account.has_value())) {
        return account.value().balance;
    }
    return 0;
}

uint256_t State::get_original_balance(monad_address const &address)
{
    return original_account_state(address).get_balance_pessimistic();
}

bytes32_t State::get_code_hash(monad_address const &address)
{
    auto const &account = recent_account(address);
    if (MONAD_LIKELY(account.has_value())) {
        return account.value().code_hash;
    }
    return NULL_HASH;
}

bool State::is_destructed(monad_address const &address)
{
    auto const &account_state = recent_account_state(address);
    return account_state.is_destructed();
}

bool State::is_current_incarnation(monad_address const &address)
{
    auto const &account = recent_account(address);
    if (MONAD_LIKELY(account.has_value())) {
        return account.value().incarnation == incarnation_;
    }
    return false;
}

template <typename Output>
inline void State::current_storage_into(
    AccountState const &account_state, monad_address const &address,
    bytes32_t const &key, Output &out)
{
    auto const write_value = [&out](bytes32_t const &value) {
        if constexpr (std::is_same_v<Output, uint256_t>) {
            out = load_be<uint256_t>(value);
        }
        else {
            out = value;
        }
    };
    auto const &account = account_state.account_;
    MONAD_ASSERT(account.has_value());
    auto const &storage = account_state.storage_;
    if (auto const *const stored_value = storage.find(key); stored_value) {
        write_value(*stored_value);
        return;
    }
    MONAD_ASSERT(account_state.original_state_ != nullptr);
    auto &original_account_state = *account_state.original_state_;
    auto const &original_account = original_account_state.account_;
    if (!original_account.has_value() ||
        account.value().incarnation != original_account.value().incarnation) {
        out = {};
        return;
    }
    auto &original_storage = original_account_state.prestate_storage_;
    if (auto const *const original_value = original_storage.find(key);
        original_value) {
        write_value(*original_value);
    }
    else {
#ifdef MONAD_ZKVM_ZISK
        bytes32_t const &value = block_state_.read_storage(
            *original_account_state.block_delta_,
            address,
            account.value().incarnation,
            key);
        original_account_state.cached_slots_may_be_cold_ = 1;
#else
        bytes32_t const value = block_state_.read_storage(
            address, account.value().incarnation, key);
#endif
        original_storage.insert(key, value);
        write_value(value);
    }
}

void State::get_storage_into(
    monad_address const &address, bytes32_t const &key, bytes32_t &out)
{
    AccountState *current_state = cached_current_account(address);
    if (current_state == nullptr) {
        auto const it = current_.find(address);
        if (it != current_.end()) {
            current_state = &it->second;
        }
    }
    if (current_state == nullptr) {
        auto const it2 = original_.find(address);
        MONAD_ASSERT(it2 != original_.end());
        auto &account_state = it2->second;
        auto const &account = account_state.account_;
        MONAD_ASSERT(account.has_value());
        auto &storage = account_state.prestate_storage_;
        if (auto const *const it3 = storage.find(key); it3) {
            out = *it3;
        }
        else {
#ifdef MONAD_ZKVM_ZISK
            bytes32_t const &value = block_state_.read_storage(
                *account_state.block_delta_,
                address,
                account.value().incarnation,
                key);
            account_state.cached_slots_may_be_cold_ = 1;
#else
            bytes32_t const value = block_state_.read_storage(
                address, account.value().incarnation, key);
#endif
            storage.insert(key, value);
            out = value;
        }
    }
    else {
        current_storage_into(*current_state, address, key, out);
    }
}

bytes32_t
State::get_transient_storage(monad_address const &address, bytes32_t const &key)
{
    return recent_account_state(address).get_transient_storage(key);
}

bool State::is_touched(monad_address const &address)
{
    auto const it = current_.find(address);
    return it != current_.end() && it->second.is_touched();
}

void State::set_nonce(monad_address const &address, uint64_t const nonce)
{
    auto &account_state = current_account_state(address);
    auto &account = account_state.account_;
    if (MONAD_UNLIKELY(!account.has_value())) {
        journal_account(address, account_state);
        account = Account{.incarnation = incarnation_};
    }
    else {
        journal_nonce(address, account->nonce);
    }
    account.value().nonce = nonce;
}

void State::add_to_balance(monad_address const &address, uint256_t const &delta)
{
    auto &account_state = current_account_state(address);
    auto &account = account_state.account_;
    if (MONAD_UNLIKELY(!account.has_value())) {
        journal_account(address, account_state);
        account = Account{.incarnation = incarnation_};
    }

    // Skip unchanged balances, but still touch the account and notify rb_.
    if (delta != 0) {
        MONAD_ASSERT_THROW(
            std::numeric_limits<uint256_t>::max() - delta >=
                account.value().balance,
            "balance overflow");

        journal_balance(address, account.value().balance);
        account.value().balance += delta;
    }
    if (account_state.touch()) {
        journal_flag(address, Undo::Kind::FlagTouched);
    }
    if (rb_.tracking_enabled()) {
        rb_.on_credit(Address{address});
    }
}

void State::subtract_from_balance(
    monad_address const &address, uint256_t const &delta)
{
    auto &account_state = current_account_state(address);
    auto &account = account_state.account_;
    if (MONAD_UNLIKELY(!account.has_value())) {
        journal_account(address, account_state);
        account = Account{.incarnation = incarnation_};
    }

    // Skip unchanged balances, but still touch the account and notify rb_.
    if (delta != 0) {
        MONAD_ASSERT_THROW(
            delta <= account.value().balance, "balance underflow");

        journal_balance(address, account.value().balance);
        account.value().balance -= delta;
    }
    if (account_state.touch()) {
        journal_flag(address, Undo::Kind::FlagTouched);
    }
    if (rb_.tracking_enabled()) {
        rb_.on_debit(Address{address});
    }
}

#if defined(MONAD_ZKVM_ZISK)
StorageStatus State::set_storage(
    monad_address const &address, bytes32_t const &key, bytes32_t const &value)
{
    auto &account_state = current_account_state(address);
    // Written without being warmed, unlike an SSTORE's slot: see
    // OriginalAccountState::cached_slots_may_be_cold_.
    MONAD_ASSERT(account_state.original_state_ != nullptr);
    account_state.original_state_->cached_slots_may_be_cold_ = 1;
    return set_storage_of(account_state, address, key, value);
}

inline StorageStatus State::set_storage_of(
    AccountState &account_state, monad_address const &address,
    bytes32_t const &key, bytes32_t const &value)
{
    // Reuse cached values for journaling and storage-status computation.
    MONAD_ASSERT(account_state.original_state_ != nullptr);
    return set_storage_with_cached_values(
        account_state,
        address,
        key,
        value,
        account_state.storage_.find(key),
        account_state.original_state_->prestate_storage_.find(key));
}

inline StorageStatus State::set_storage_with_cached_values(
    AccountState &account_state, monad_address const &address,
    bytes32_t const &key, bytes32_t const &value,
    bytes32_t const *const stored_value,
    bytes32_t const *const cached_original_value)
{
    MONAD_ASSERT(account_state.account_);
    // Borrow the original value from its cache or the block state.
    bytes32_t const *original_value = cached_original_value;
    if (original_value == nullptr) {
        auto &orig_account_state = *account_state.original_state_;
        Incarnation const incarnation = account_state.account_->incarnation;
        bytes32_t const &stored = block_state_.read_storage(
            *orig_account_state.block_delta_, address, incarnation, key);
        orig_account_state.prestate_storage_.insert(key, stored);
        original_value = &stored;
    }
    journal_slot(address, key, stored_value);
    return account_state.set_storage(key, value, *original_value, stored_value);
}
#else
StorageStatus State::set_storage(
    monad_address const &address, bytes32_t const &key, bytes32_t const &value)
{
    bytes32_t original_value;
    auto &account_state = current_account_state(address);
    MONAD_ASSERT(account_state.account_);
    // Reuse this value for journalling and storage-status computation.
    // The separate pre-state cache cannot invalidate this pointer; the
    // eventual upsert still performs its own lookup.
    bytes32_t const *const stored_value = account_state.storage_.find(key);
    // original
    {
        MONAD_ASSERT(account_state.original_state_ != nullptr);
        auto &orig_account_state = *account_state.original_state_;
        auto &storage = orig_account_state.prestate_storage_;
        if (auto const *const it = storage.find(key); it) {
            original_value = *it;
        }
        else {
            Incarnation const incarnation = account_state.account_->incarnation;
            bytes32_t const value =
                block_state_.read_storage(address, incarnation, key);
            storage.insert(key, value);
            original_value = value;
        }
    }
    // state
    {
        journal_slot(address, key, stored_value);
        auto const result =
            account_state.set_storage(key, value, original_value, stored_value);
        return result;
    }
}
#endif

void State::set_transient_storage(
    monad_address const &address, bytes32_t const &key, bytes32_t const &value)
{
    auto &account_state = current_account_state(address);
#ifdef MONAD_ZKVM_ZISK
    // Find once, save the old value for rollback, then update the same slot.
    auto &transient_storage = account_state.transient_storage_;
    bytes32_t *const stored_value = transient_storage.find_mut(key);
    if (journalling()) {
        static constexpr bytes32_t zero{};
        undo_.emplace_back(address, Undo::Kind::Transient, undo_slots_.size());
        undo_slots_.emplace_back(
            key, stored_value ? *stored_value : zero, stored_value != nullptr);
    }
    if (stored_value != nullptr) {
        *stored_value = value;
    }
    else {
        transient_storage.insert_absent(key, value);
    }
#else
    journal_transient(address, account_state, key);
    account_state.set_transient_storage(key, value);
#endif
}

void State::touch(monad_address const &address)
{
    auto &account_state = current_account_state(address);
    if (account_state.touch()) {
        journal_flag(address, Undo::Kind::FlagTouched);
    }
}

#if defined(MONAD_ZKVM_ZISK)
void State::defer_beneficiary()
{
    defers_beneficiary_ = block_state_.beneficiary_deferral_enabled();
}

bool State::defer_beneficiary_credit(uint256_t const &reward)
{
    // With a row, add_to_balance credits it where the merge will find it. A
    // zero fee is no credit but a touch, which can delete an empty account.
    if (!defers_beneficiary_ || beneficiary_row_created_ || reward == 0) {
        return false;
    }
    // No row: the beneficiary's entry is the one the transaction began with,
    // and the merge leaves it as it is, so the fee commutes with the
    // transactions that follow until one of them reads it.
    block_state_.defer_beneficiary_credit(reward, incarnation_);
    return true;
}

#endif
AccessStatus State::access_account(monad_address const &address)
{
    auto &account_state = current_account_state(address);
    auto const status = account_state.access();
    if (status == AccessStatus::Cold) {
        journal_flag(address, Undo::Kind::FlagAccessed);
    }
    return status;
}

template <Traits traits>
[[gnu::always_inline]] inline AccessStatus State::access_storage_of(
    AccountState &account_state, monad_address const &address,
    bytes32_t const &key)
{
    auto const slot_status = account_state.access_storage(key);
    if (slot_status == AccessStatus::Cold) {
#ifdef MONAD_ZKVM_ZISK
        journal_warm_slot(address);
#else
        journal_warm_slot(address, key);
#endif
    }
    if constexpr (traits::mip_8_active()) {
        journal_pages(address, account_state);
        return account_state.page_tracker_.access_page(key);
    }
    return slot_status;
}

template <Traits traits>
AccessStatus
State::access_storage(monad_address const &address, bytes32_t const &key)
{
    return access_storage_of<traits>(
        current_account_state(address), address, key);
}

EXPLICIT_TRAITS_MEMBER(State::access_storage);

#if defined(MONAD_ZKVM_ZISK)
// Warm and read the slot using the same account lookup.
template <Traits traits>
AccessStatus State::sload_full(
    monad_address const &address, bytes32_t const &key,
    bool const can_pay_cold_access, uint256_t &out)
{
    auto &account_state = current_account_state(address);
    AccessStatus const status =
        access_storage_of<traits>(account_state, address, key);
    if (status == AccessStatus::Warm || can_pay_cold_access) {
        current_storage_into(account_state, address, key, out);
    }
    return status;
}

AccessStatus State::sload_cold(
    monad_address const &address, bytes32_t const &key,
    bool const can_pay_cold_access, uint256_t &out, AccountState &account_state)
{
    account_state.add_accessed_storage(key);
    journal_warm_slot(address);
    if (can_pay_cold_access) {
        current_storage_into(account_state, address, key, out);
    }
    return AccessStatus::Cold;
}

// Both value caches missed; warm the slot and read the block directly.
AccessStatus State::sload_cold_uncached(
    monad_address const &address, bytes32_t const &key,
    bool const can_pay_cold_access, uint256_t &out, AccountState &account_state)
{
    account_state.add_accessed_storage(key);
    journal_warm_slot(address);
    if (can_pay_cold_access) {
        OriginalAccountState &original_state = *account_state.original_state_;
        bytes32_t const &value = block_state_.read_storage(
            *original_state.block_delta_,
            address,
            original_state.account_.value().incarnation,
            key);
        original_state.prestate_storage_.insert(key, value);
        out = load_be<uint256_t>(value);
    }
    return AccessStatus::Cold;
}

// The caller checked that the current and original incarnations match.
AccessStatus State::sload_read(
    monad_address const &address, bytes32_t const &key, uint256_t &out,
    OriginalAccountState &original_state)
{
    bytes32_t const &value = block_state_.read_storage(
        *original_state.block_delta_,
        address,
        original_state.account_.value().incarnation,
        key);
    original_state.prestate_storage_.insert(key, value);
    out = load_be<uint256_t>(value);
    return AccessStatus::Warm;
}

// Answer cached warm reads without calls. Keep slower paths out of line so
// they can be tail-called without adding register saves to the fast path.
template <Traits traits>
AccessStatus State::sload_into(
    monad_address const &address, bytes32_t const &key,
    bool const can_pay_cold_access, uint256_t &out)
{
    if constexpr (!traits::mip_8_active()) {
        AccountState *const current_state =
            cached_current_account_in_frame(address);
        if (MONAD_LIKELY(current_state != nullptr)) {
            auto const &account = current_state->account_;
            OriginalAccountState *const original_state =
                current_state->original_state_;
            // Missing accounts or original state use the general path below.
            if (MONAD_LIKELY(
                    account.has_value() && original_state != nullptr)) {
                auto const &original_account = original_state->account_;
                // Cached values prove warmth only while this invariant holds.
                // Original storage also requires a matching incarnation.
                if (MONAD_LIKELY(
                        original_state->cached_slots_may_be_cold_ == 0)) {
                    if (auto const *const cached_value =
                            current_state->storage_.find(key);
                        cached_value) {
                        out = load_be<uint256_t>(*cached_value);
                        return AccessStatus::Warm;
                    }
                    if (MONAD_LIKELY(
                            original_account.has_value() &&
                            account.value().incarnation ==
                                original_account.value().incarnation)) {
                        if (auto const *const cached_value =
                                original_state->prestate_storage_.find(key);
                            cached_value) {
                            out = load_be<uint256_t>(*cached_value);
                            return AccessStatus::Warm;
                        }
                        if (!current_state->is_accessed_storage(key)) {
                            return sload_cold_uncached(
                                address,
                                key,
                                can_pay_cold_access,
                                out,
                                *current_state);
                        }
                        return sload_read(address, key, out, *original_state);
                    }
                }
                if (!current_state->is_accessed_storage(key)) {
                    return sload_cold(
                        address, key, can_pay_cold_access, out, *current_state);
                }
                // current_storage_into, up to a read of the block's state.
                if (auto const *const cached_value =
                        current_state->storage_.find(key);
                    cached_value) {
                    out = load_be<uint256_t>(*cached_value);
                    return AccessStatus::Warm;
                }
                if (!original_account.has_value() ||
                    account.value().incarnation !=
                        original_account.value().incarnation) {
                    out = uint256_t{};
                    return AccessStatus::Warm;
                }
                if (auto const *const cached_value =
                        original_state->prestate_storage_.find(key);
                    cached_value) {
                    out = load_be<uint256_t>(*cached_value);
                    return AccessStatus::Warm;
                }
                return sload_read(address, key, out, *original_state);
            }
        }
    }
    return sload_full<traits>(address, key, can_pay_cold_access, out);
}

EXPLICIT_TRAITS_MEMBER(State::sload_into);

template <Traits traits>
vm::runtime::SstoreStatus State::sstore_into(
    monad_address const &address, bytes32_t const &key, bytes32_t const &value,
    bool const can_pay_cold_access)
{
    auto &account_state = current_account_state(address);
    if constexpr (!traits::mip_8_active()) {
        // Reuse the value lookups for both warmth and the eventual write.
        MONAD_ASSERT(account_state.original_state_ != nullptr);
        OriginalAccountState const &original_state =
            *account_state.original_state_;
        bytes32_t const *const stored_value = account_state.storage_.find(key);
        bytes32_t const *const cached_original_value =
            original_state.prestate_storage_.find(key);
        AccessStatus access = AccessStatus::Warm;
        if ((stored_value == nullptr && cached_original_value == nullptr) ||
            original_state.cached_slots_may_be_cold_ != 0) {
            access = access_storage_of<traits>(account_state, address, key);
            if (access == AccessStatus::Cold && !can_pay_cold_access) {
                return {access, StorageStatus::Assigned};
            }
        }
        return {
            access,
            set_storage_with_cached_values(
                account_state,
                address,
                key,
                value,
                stored_value,
                cached_original_value)};
    }
    else {
        AccessStatus const access =
            access_storage_of<traits>(account_state, address, key);
        if (access == AccessStatus::Cold && !can_pay_cold_access) {
            return {access, StorageStatus::Assigned};
        }
        return {access, set_storage_of(account_state, address, key, value)};
    }
}

EXPLICIT_TRAITS_MEMBER(State::sstore_into);
#endif

PageStorageStatus State::update_page(
    monad_address const &address, bytes32_t const &key,
    StorageStatus const status)
{
    auto &account_state = current_account_state(address);
    journal_pages(address, account_state);
    return account_state.page_tracker_.update_page(key, status);
}

template <Traits traits>
bool State::selfdestruct_to_self_burns(
    [[maybe_unused]] monad_address const &address)
{
    if constexpr (!traits::eip_6780_active()) {
        return true;
    }
    else if constexpr (traits::eip_8246_active()) {
        return false;
    }
    else {
        return is_current_incarnation(address);
    }
}

template <Traits traits>
std::pair<bool, uint256_t> State::selfdestruct(
    monad_address const &address, monad_address const &beneficiary)
{
    auto &account_state = current_account_state(address);
    uint256_t const balance = get_balance(address);

    if (!address_equal(address, beneficiary)) {
        add_to_balance(beneficiary, balance);
        subtract_from_balance(address, balance);
    }
    else if (selfdestruct_to_self_burns<traits>(address)) {
        subtract_from_balance(address, balance);
    }

    bool const inserted = account_state.destruct();
    if (inserted) {
        journal_flag(address, Undo::Kind::FlagDestructed);
    }
    // Recompute reserve-balance status after setting the destructed flag.
    if (rb_.tracking_enabled()) {
        rb_.on_debit(Address{address});
    }
    return {inserted, balance};
}

EXPLICIT_TRAITS_MEMBER(State::selfdestruct);

// Overwrite every slot this transaction touched with zero: a slot only read has
// an entry in the original map, a slot written has one in both. Zero rather
// than remove, since a missing entry reads through to the pre-destruct value.
void State::zero_storage(
    monad_address const &address, AccountState &account_state)
{
    auto const orig = original_.find(address);
    MONAD_ASSERT(orig != original_.end());
    AccountState::StorageMap zeroed;
    for (auto const &kv : orig->second.prestate_storage_) {
        zeroed.upsert(kv.first, bytes32_t{});
    }
    for (auto const &kv : account_state.storage_) {
        zeroed.upsert(kv.first, bytes32_t{});
    }
    account_state.storage_ = std::move(zeroed);
}

// YP (87)
template <Traits traits>
void State::destruct_suicides()
{
    MONAD_ASSERT(!version_);

    for (auto &it : current_) {
        auto &account_state = it.second;
        if (MONAD_LIKELY(!account_state.is_destructed())) {
            continue;
        }
        auto &account = account_state.account_;

        if constexpr (!traits::eip_6780_active()) {
            account.reset();
            continue;
        }

        // EIP-6780: only an account created in this transaction is destroyed.
        if (account->incarnation != incarnation_) {
            continue;
        }

        if constexpr (!traits::eip_8246_active()) {
            account.reset();
            continue;
        }

        // EIP-8246: nonce reset, code and storage cleared, balance unchanged.
        // Leaving the incarnation as is will clear the old storage.
        account->nonce = 0;
        account->code_hash = NULL_HASH;
        if (is_empty(*account)) { // EIP-161
            account.reset();
            continue;
        }
        zero_storage(it.first, account_state);
    }
}

EXPLICIT_TRAITS_MEMBER(State::destruct_suicides);

// YP (88)
void State::destruct_touched_dead()
{
    MONAD_ASSERT(!version_);
    // All frames must be closed, including those that touched no accounts: an
    // unbalanced push leaves a mark behind even when no row was touched.
    MONAD_ASSERT(
        undo_.empty() && undo_accounts_.empty() && undo_words_.empty() &&
        undo_u64_.empty() && undo_slots_.empty() && undo_pages_.empty() &&
        undo_marks_.empty());

    for (auto &it : current_) {
        auto &account_state = it.second;
        if (MONAD_LIKELY(!account_state.is_touched())) {
            continue;
        }
        auto &account = account_state.account_;
        if (is_dead(account)) {
            account.reset();
        }
    }
}

vm::SharedVarcode const &State::read_code_ref(bytes32_t const &code_hash)
{
    {
        auto const it = code_.find(code_hash);
        if (it != code_.end()) {
            return it->second;
        }
    }
#if defined(MONAD_ZKVM_VARCODE_CACHE)
    return block_state_.read_code_ref(code_hash);
#else
    borrowed_code_ = block_state_.read_code(code_hash);
    return borrowed_code_;
#endif
}

vm::SharedVarcode State::read_code(bytes32_t const &code_hash)
{
    return read_code_ref(code_hash);
}

vm::SharedVarcode State::get_code(monad_address const &address)
{
    auto const &account = recent_account(address);
    if (MONAD_UNLIKELY(!account.has_value())) {
        return block_state_.read_code(NULL_HASH);
    }
    return read_code(account.value().code_hash);
}

#if defined(MONAD_ZKVM_ZISK) && defined(MONAD_ZKVM_VARCODE_CACHE)
State::AccountCode State::account_code(monad_address const &address)
{
    auto *const cached = cached_current_account(address);
    auto const [visible, original] =
        cached ? AccountReadRows{cached, cached->original_state_}
               : rows_for_read(address);
    if (MONAD_UNLIKELY(!visible->account_)) {
        return {NULL_HASH, nullptr};
    }
    auto const &hash = visible->account_->code_hash;
    // Keep the cache in the block entry, but match the currently visible hash.
    // Rollback needs no cache undo: a different hash forces a fresh lookup.
    StateDelta &entry = *original->block_delta_;
    if (entry.cached_code && entry.cached_code_hash == hash) {
        return {hash, entry.cached_code};
    }
    // Transaction-local entries cannot be borrowed by the block.
    if (auto const it = code_.find(hash); it != code_.end()) {
        return {hash, &it->second};
    }
    entry.cached_code = &block_state_.read_code_ref(hash);
    entry.cached_code_hash = hash;
    return {hash, entry.cached_code};
}
#endif

size_t State::get_code_size(monad_address const &address)
{
#if defined(MONAD_ZKVM_ZISK) && defined(MONAD_ZKVM_VARCODE_CACHE)
    auto const lookup = account_code(address);
    if (MONAD_UNLIKELY(lookup.code == nullptr)) {
        return 0;
    }
    auto const &vcode = *lookup.code;
#else
    auto const &account = recent_account(address);
    if (MONAD_UNLIKELY(!account.has_value())) {
        return 0;
    }
    vm::SharedVarcode const &vcode = read_code_ref(account.value().code_hash);
#endif
    MONAD_ASSERT(vcode);
    return vcode->intercode()->size();
}

size_t State::copy_code(
    monad_address const &address, size_t const offset, uint8_t *const buffer,
    size_t const buffer_size)
{
#if defined(MONAD_ZKVM_ZISK) && defined(MONAD_ZKVM_VARCODE_CACHE)
    auto const lookup = account_code(address);
    if (MONAD_UNLIKELY(lookup.code == nullptr)) {
        return 0;
    }
    auto const &vcode = *lookup.code;
#else
    auto const &account = recent_account(address);
    if (MONAD_UNLIKELY(!account.has_value())) {
        return 0;
    }
    vm::SharedVarcode const &vcode = read_code_ref(account.value().code_hash);
#endif
    MONAD_ASSERT(vcode);
    return vcode->intercode()->copy_code(offset, buffer, buffer_size);
}

#if defined(MONAD_ZKVM_ZISK)
std::optional<Address> State::delegate_of(monad_address const &address)
{
    #if defined(MONAD_ZKVM_ZISK) && defined(MONAD_ZKVM_VARCODE_CACHE)
    auto const lookup = account_code(address);
    if (MONAD_UNLIKELY(lookup.code == nullptr)) {
        return std::nullopt;
    }
    auto const &vcode = *lookup.code;
    #else
    auto const &account = recent_account(address);
    if (MONAD_UNLIKELY(!account.has_value())) {
        return std::nullopt;
    }
    vm::SharedVarcode const &vcode = read_code_ref(account.value().code_hash);
    #endif
    MONAD_ASSERT(vcode);
    return vm::evm::designation_of(vcode->intercode()->code_span());
}
#endif

void State::set_code(monad_address const &address, byte_string_view const code)
{
    auto &account = current_account(address);
    if (MONAD_UNLIKELY(!account.has_value())) {
        return;
    }

    auto const code_hash = to_bytes(keccak256(code));
    code_[code_hash] = vm().try_insert_varcode_raw(code_hash, code);
    journal_code_hash(address, account.value().code_hash);
    account.value().code_hash = code_hash;
    if (rb_.tracking_enabled()) {
        rb_.on_set_code(Address{address}, code);
    }
}

void State::create_contract(monad_address const &address)
{
    auto &account_state = current_account_state(address);
    auto &account = account_state.account_;
    // Save account_ to restore presence and incarnation on rollback.
    journal_account(address, account_state);
    if (MONAD_UNLIKELY(account.has_value())) {
        // EIP-684
        MONAD_ASSERT(account->nonce == 0);
        MONAD_ASSERT(account->code_hash == NULL_HASH);
        // keep the balance, per chapter 7 of the YP
        account->incarnation = incarnation_;
    }
    else {
        account = Account{.incarnation = incarnation_};
    }
}

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
void State::create_account_no_rollback(monad_address const &address)
{
    auto &account_state = current_account_state(address);
    auto &account = account_state.account_;
    // The name refers to SELFDESTRUCT protection; frame rejection still
    // restores the previous account.
    journal_account(address, account_state);
    MONAD_ASSERT(!account.has_value());
    account = Account{
        .incarnation = Incarnation{
            incarnation_.get_block(),
            Incarnation::LAST_TX,
        }};
}

std::vector<Receipt::Log> const &State::logs()
{
    return logs_;
}

std::vector<Receipt::Log> State::take_logs()
{
    return std::exchange(logs_, {});
}

void State::store_log(Receipt::Log const &log)
{
    logs_.push_back(log);
}

void State::store_log(Receipt::Log &&log)
{
    logs_.push_back(std::move(log));
}

void State::set_to_state_incarnation(monad_address const &address)
{
    auto &account_state = current_account_state(address);
    auto &account = account_state.account_;
    journal_account(address, account_state);
    if (MONAD_UNLIKELY(!account.has_value())) {
        account = Account{.incarnation = incarnation_};
    }
    account.value().incarnation = incarnation_;
}

// RELAXED MERGE
// if original and current can be adjusted to satisfy min balance, adjust
// both values for merge
bool State::try_fix_account_mismatch(
    monad_address const &address, std::optional<Account> const &actual)
{
    auto const original_it = original_.find(address);
    MONAD_ASSERT(original_it != original_.end());
    OriginalAccountState &original_state = original_it->second;
    auto &original = original_state.account_;
    // verify original used and original found are otherwise the same
    if (is_dead(original)) {
        return false;
    }
    if (is_dead(actual)) {
        return false;
    }
    if (original->code_hash != actual->code_hash) {
        return false;
    }
    if (original->incarnation != actual->incarnation) {
        return false;
    }
    if (original->nonce != actual->nonce) {
        return false;
    }
    MONAD_ASSERT(original->balance != actual->balance);
    // is relaxed merge disabled
    if (!relaxed_validation_) {
        return false;
    }
    if (original_state.validate_exact_balance()) {
        return false;
    }
    // original balance does not meet min required
    if (actual->balance < original_state.min_balance()) {
        return false;
    }
    // adjust balances
    auto const current_it = current_.find(address);
    if (current_it != current_.end()) {
        auto &recent_state = current_it->second;
        auto &recent = recent_state.account_;
        if (!recent) {
            return false;
        }
        if (actual->balance > original->balance) {
            recent->balance += actual->balance - original->balance;
        }
        else {
            MONAD_ASSERT(
                recent->balance >= (original->balance - actual->balance));
            recent->balance -= original->balance - actual->balance;
        }
    }
    original->balance = actual->balance;

    // not necessary as can_merge() wont be called
    // anymore, but just being defensive, and this makes
    // it easier to write the class invariant
    original_state.set_validate_exact_balance();
    return true;
}

bool State::record_balance_constraint_for_debit(
    monad_address const &address, uint256_t const &debit)
{
#if defined(MONAD_ZKVM_NO_MERGE_CONSTRAINTS)
    // Keep the balance check; sequential execution needs no merge constraints.
    // Any balance covers a zero debit; skip the account lookup.
    if (debit == 0) {
        return true;
    }
    auto const &account = recent_account(address);
    uint256_t const balance = account.has_value() ? account->balance : 0;
    return balance >= debit;
#else
    auto const [visible, original] = rows_for_read(address);
    auto const &account = visible->account_;
    uint256_t const balance = account.has_value() ? account->balance : 0;

    auto &original_state = *original;
    // RELAXED MERGE
    // if current balance  >= `debit`, then:
    // 1. compute the amount that current balance exceeds `debit`
    // 2. require that the original balance at merge time is at least the
    // original balance used during this execution less said excess
    if (balance >= debit) {
        uint256_t const diff = balance - debit;
        auto const &original = original_state.account_;
        uint256_t const original_balance =
            original.has_value() ? original->balance : 0;
        if (original_balance > diff) { // avoid underflow when <= diff
            uint256_t const min_balance =
                original_balance -
                diff; // original balance - current balance + debit
            original_state.set_min_balance(min_balance);
        }
        return true;
    }

    // otherwise require that original balance at merge time matches
    // original balance used during this execution exactly
    original_state.set_validate_exact_balance();
    return false;
#endif
}

MONAD_NAMESPACE_END
