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
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <evmc/evmc.h>

#include <immer/vector.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

#ifdef MONAD_ZKVM_KECCAK_SITES
#include <category/core/keccak_sites.hpp>
#else
#define MONAD_GUEST_SITE(s) ((void)0)
#define MONAD_GUEST_ADD2(s, v) ((void)0)
#endif

MONAD_NAMESPACE_BEGIN

OriginalAccountState &State::original_account_state(Address const &address)
{
    auto it = original_.find(address);
    if (it == original_.end()) {
        // block state
        auto const account = block_state_.read_account(address);
        it = original_.try_emplace(address, account).first;
    }
    return it->second;
}

AccountState const &State::recent_account_state(Address const &address)
{
    // current
    auto const it = current_.find(address);
    if (it != current_.end()) {
        return it->second;
    }
    // original
    return original_account_state(address);
}

AccountState &State::current_account_state(Address const &address)
{
    MONAD_GUEST_SITE(ACCT_LOOKUP);

    // Repeat access to the same account is the common case (64.9% measured), and both the map
    // lookup and the dirty-set insert are then already done. The insert is idempotent, so skipping
    // it leaves the frame's dirty set identical -- provided the epoch says we are still in the
    // frame that recorded it.
    if (memo_val_ != nullptr &&
        __builtin_memcmp(address.bytes, memo_addr_.bytes, sizeof(address.bytes)) == 0) {
        MONAD_GUEST_SITE(ACCT_MEMO_HIT);
        if (memo_epoch_ != frame_epoch_) {
            if (!dirty_.empty()) {
                MONAD_GUEST_SITE(DIRTY_EMPLACE);
                // Same decision as the slow path, and it must journal for the same reason: a
                // memo hit is still this frame's first touch of that row when the epoch moved.
                if (dirty_.back().emplace(address)) {
                    journal_first_touch(address, *memo_val_, false);
                }
            }
            memo_epoch_ = frame_epoch_;
        }
        return *memo_val_;
    }

    // current
    auto it = current_.find(address);
    bool created = false;
    if (MONAD_UNLIKELY(it == current_.end())) {
        MONAD_GUEST_SITE(ACCT_FIND_MISS);
        // original
        auto const &account_state = original_account_state(address);
        it = current_.try_emplace(address, account_state).first;
        created = true;
    }
    if (!dirty_.empty()) {
        MONAD_GUEST_SITE(DIRTY_EMPLACE);
        if (dirty_.back().emplace(address)) {
            journal_first_touch(address, it->second, created);
        }
    }
    memo_addr_ = address;
    memo_val_ = &it->second;
    memo_epoch_ = frame_epoch_;
    return it->second;
}

// One undo record per (frame, row). `dirty_` already answers "is this row new to this frame", so
// the insert's own return value is the trigger: journal exactly when it reports the address as
// newly listed. A row this frame CREATED cannot be restored -- there was nothing before it -- so
// its record says erase.
void State::journal_first_touch(
    Address const &address, AccountState const &row, bool const created)
{
    undo_.push_back(
        Undo{address, created ? std::nullopt : std::optional<AccountState>{row}});
}

std::optional<Account> &State::current_account(Address const &address)
{
    return current_account_state(address).account_;
}

State::State(
    BlockState &block_state, Incarnation const incarnation,
    bool const relaxed_validation)
    : block_state_{block_state}
    , incarnation_{incarnation}
    , relaxed_validation_{relaxed_validation}
    , rb_{this}
{
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

DirtyAccounts const &State::current_frame_dirty_accounts() const
{
    MONAD_ASSERT(version_);
    MONAD_ASSERT(dirty_.size() == version_);

    return dirty_.back();
}

void State::push()
{
    MONAD_ASSERT(dirty_.size() == version_);

    ++frame_epoch_;

    ++version_;
    dirty_.emplace_back();
    undo_marks_.push_back(undo_.size());
    log_marks_.push_back(logs_.size());
}

void State::pop_accept()
{
    MONAD_ASSERT(version_);
    MONAD_ASSERT(dirty_.size() == version_);

    ++frame_epoch_;
    MONAD_GUEST_SITE(POP_ACCEPT);
    MONAD_GUEST_ADD2(POP_ACCEPT, version_);
#ifdef MONAD_ZKVM_KECCAK_SITES
    // Everything this frame leaves behind now belongs to the parent's mark.
    if (undo_marks_.size() > 1) {
        for (size_t i = undo_marks_.back(); i < undo_.size(); ++i) {
            undo_[i].promoted = true;
        }
    }
#endif

    auto accounts = std::move(dirty_.back());
    dirty_.pop_back();
    // Accepted: the rows keep the values this frame gave them. What the parent needs is the
    // knowledge that they changed -- so its dirty list gains them, and this frame's undo records
    // simply stay in the log under the parent's mark. Replayed backwards they restore the
    // pre-PARENT value, because a row this frame was the first to touch was, by construction,
    // untouched by the parent too.
    for (auto const &dirty_address : accounts) {
        if (!dirty_.empty()) {
            dirty_.back().emplace(dirty_address);
        }
    }
    undo_marks_.pop_back();
    // With no mark left there is nothing that could roll back past this point, so the records are
    // dead. Dropping them is not housekeeping: without it the log grows by one 160-byte record per
    // account per frame for the whole block, and the invariant at the end of the block -- that an
    // empty log means every frame closed -- would never hold.
    if (undo_marks_.empty()) {
        undo_.clear();
    }

    // Accepted: the frame's logs stay where they are, only its watermark goes.
    log_marks_.pop_back();

    --version_;
}

void State::pop_reject()
{
    MONAD_ASSERT(version_);
    MONAD_ASSERT(dirty_.size() == version_);

    ++frame_epoch_;
    MONAD_GUEST_SITE(POP_REJECT);
    MONAD_GUEST_ADD2(DIRTY_EMPLACE, version_);

    auto accounts = std::move(dirty_.back());
    dirty_.pop_back();

    // Rejected: drop exactly what this frame appended.
    logs_.resize(log_marks_.back());
    log_marks_.pop_back();

    // erase() moves the last element into the hole, and a restore rewrites a row in place, so any
    // pointer into current_ is stale from here on.
    memo_val_ = nullptr;

    // Replay BACKWARDS: a row touched by this frame and by one nested inside it carries two
    // records, and the older value has to land last.
    size_t const mark = undo_marks_.back();
    undo_marks_.pop_back();
    while (undo_.size() > mark) {
        Undo &u = undo_.back();
        MONAD_GUEST_ADD2(POP_REJECT, 1);
#ifdef MONAD_ZKVM_KECCAK_SITES
        if (u.promoted) {
            MONAD_GUEST_ADD2(STOR_LOOKUP, 1);
        }
#endif
        if (!u.prev) {
            MONAD_GUEST_ADD2(ACCT_FIND_MISS, 1);
            current_.erase(u.addr);
        }
        else {
            auto const it = current_.find(u.addr);
            MONAD_ASSERT(it != current_.end());
#ifdef MONAD_ZKVM_KECCAK_SITES
            // The value being discarded: did this frame destruct the account?
            if (it->second.is_destructed() && !u.prev->is_destructed()) {
                MONAD_GUEST_ADD2(ACCT_MEMO_HIT, 1);
            }
#endif
            it->second = std::move(*u.prev);
        }
        undo_.pop_back();
    }
    if (undo_marks_.empty()) {
        undo_.clear();
    }

    rb_.on_pop_reject(accounts.span());

    --version_;
}

vm::VM &State::vm()
{
    return block_state_.vm();
}

std::optional<Account> const &State::recent_account(Address const &address)
{
    return recent_account_state(address).account_;
}

void State::set_original_nonce(Address const &address, uint64_t const nonce)
{
    auto &account_state = original_account_state(address);
    auto &account = account_state.account_;
    if (!account.has_value()) {
        account = Account{};
    }
    account->nonce = nonce;
}

bool State::account_exists(Address const &address)
{
    return recent_account(address).has_value();
}

bool State::account_is_dead(Address const &address)
{
    return is_dead(recent_account(address));
}

uint64_t State::get_nonce(Address const &address)
{
    auto const &account = recent_account(address);
    if (MONAD_LIKELY(account.has_value())) {
        return account.value().nonce;
    }
    return 0;
}

uint256_t State::get_balance(Address const &address)
{
    auto const &account = recent_account(address);
    original_account_state(address).set_validate_exact_balance();
    if (MONAD_LIKELY(account.has_value())) {
        return account.value().balance;
    }
    return 0;
}

uint256_t State::get_original_balance(Address const &address)
{
    return original_account_state(address).get_balance_pessimistic();
}

bytes32_t State::get_code_hash(Address const &address)
{
    auto const &account = recent_account(address);
    if (MONAD_LIKELY(account.has_value())) {
        return account.value().code_hash;
    }
    return NULL_HASH;
}

bool State::is_destructed(Address const &address)
{
    auto const &account_state = recent_account_state(address);
    return account_state.is_destructed();
}

bool State::is_current_incarnation(Address const &address)
{
    auto const &account = recent_account(address);
    if (MONAD_LIKELY(account.has_value())) {
        return account.value().incarnation == incarnation_;
    }
    return false;
}

bytes32_t State::get_storage(Address const &address, bytes32_t const &key)
{
    MONAD_GUEST_SITE(STOR_LOOKUP);
    auto const it = current_.find(address);
    if (it == current_.end()) {
        auto const it2 = original_.find(address);
        MONAD_ASSERT(it2 != original_.end());
        auto &account_state = it2->second;
        auto const &account = account_state.account_;
        MONAD_ASSERT(account.has_value());
        auto &storage = account_state.storage_;
        if (auto const *const it3 = storage.find(key); it3) {
            return *it3;
        }
        else {
            bytes32_t const value = block_state_.read_storage(
                address, account.value().incarnation, key);
            storage = storage.insert({key, value});
            return value;
        }
    }
    else {
        auto const &account_state = it->second;
        auto const &account = account_state.account_;
        MONAD_ASSERT(account.has_value());
        auto const &storage = account_state.storage_;
        if (auto const *const it2 = storage.find(key); it2) {
            return *it2;
        }
        auto const it2 = original_.find(address);
        MONAD_ASSERT(it2 != original_.end());
        auto &original_account_state = it2->second;
        auto const &original_account = original_account_state.account_;
        if (!original_account.has_value() ||
            account.value().incarnation !=
                original_account.value().incarnation) {
            return {};
        }
        auto &original_storage = original_account_state.storage_;
        if (auto const *const it3 = original_storage.find(key); it3) {
            return *it3;
        }
        else {
            bytes32_t const value = block_state_.read_storage(
                address, account.value().incarnation, key);
            original_storage = original_storage.insert({key, value});
            return value;
        }
    }
}

bytes32_t
State::get_transient_storage(Address const &address, bytes32_t const &key)
{
    return recent_account_state(address).get_transient_storage(key);
}

bool State::is_touched(Address const &address)
{
    auto const it = current_.find(address);
    return it != current_.end() && it->second.is_touched();
}

void State::set_nonce(Address const &address, uint64_t const nonce)
{
    auto &account = current_account(address);
    if (MONAD_UNLIKELY(!account.has_value())) {
        account = Account{.incarnation = incarnation_};
    }
    account.value().nonce = nonce;
}

void State::add_to_balance(Address const &address, uint256_t const &delta)
{
    auto &account_state = current_account_state(address);
    auto &account = account_state.account_;
    if (MONAD_UNLIKELY(!account.has_value())) {
        account = Account{.incarnation = incarnation_};
    }

    MONAD_ASSERT_THROW(
        std::numeric_limits<uint256_t>::max() - delta >=
            account.value().balance,
        "balance overflow");

    account.value().balance += delta;
    account_state.touch();
    rb_.on_credit(address);
}

void State::subtract_from_balance(
    Address const &address, uint256_t const &delta)
{
    auto &account_state = current_account_state(address);
    auto &account = account_state.account_;
    if (MONAD_UNLIKELY(!account.has_value())) {
        account = Account{.incarnation = incarnation_};
    }

    MONAD_ASSERT_THROW(delta <= account.value().balance, "balance underflow");

    account.value().balance -= delta;
    account_state.touch();
    rb_.on_debit(address);
}

evmc_storage_status State::set_storage(
    Address const &address, bytes32_t const &key, bytes32_t const &value)
{
    bytes32_t original_value;
    auto &account_state = current_account_state(address);
    MONAD_ASSERT(account_state.account_);
    // original
    {
        auto &orig_account_state = original_account_state(address);
        auto &storage = orig_account_state.storage_;
        if (auto const *const it = storage.find(key); it) {
            original_value = *it;
        }
        else {
            Incarnation const incarnation = account_state.account_->incarnation;
            bytes32_t const value =
                block_state_.read_storage(address, incarnation, key);
            storage = storage.insert({key, value});
            original_value = value;
        }
    }
    // state
    {
        auto const result =
            account_state.set_storage(key, value, original_value);
        return result;
    }
}

void State::set_transient_storage(
    Address const &address, bytes32_t const &key, bytes32_t const &value)
{
    current_account_state(address).set_transient_storage(key, value);
}

void State::touch(Address const &address)
{
    auto &account_state = current_account_state(address);
    account_state.touch();
}

evmc_access_status State::access_account(Address const &address)
{
    auto &account_state = current_account_state(address);
    return account_state.access();
}

template <Traits traits>
evmc_access_status
State::access_storage(Address const &address, bytes32_t const &key)
{
    auto &account_state = current_account_state(address);
    auto const slot_status = account_state.access_storage(key);
    if constexpr (traits::mip_8_active()) {
        return account_state.page_tracker_.access_page(key);
    }
    return slot_status;
}

EXPLICIT_TRAITS_MEMBER(State::access_storage);

vm::Host::PageStorageStatus State::update_page(
    Address const &address, bytes32_t const &key,
    evmc_storage_status const status)
{
    auto &account_state = current_account_state(address);
    return account_state.page_tracker_.update_page(key, status);
}

template <Traits traits>
std::pair<bool, uint256_t>
State::selfdestruct(Address const &address, Address const &beneficiary)
{
    auto &account_state = current_account_state(address);
    uint256_t const balance = get_balance(address);

    if constexpr (traits::evm_rev() < MONAD_ETH_CANCUN) {
        if (address != beneficiary) {
            add_to_balance(beneficiary, balance);
        }
        subtract_from_balance(address, balance);
    }
    else {
        if (address != beneficiary || is_current_incarnation(address)) {
            if (address != beneficiary) {
                add_to_balance(beneficiary, balance);
            }
            subtract_from_balance(address, balance);
        }
    }

    bool const inserted = account_state.destruct();
    // Recompute reserve-balance status after setting the destructed flag.
    rb_.on_debit(address);
    return {inserted, balance};
}

EXPLICIT_TRAITS_MEMBER(State::selfdestruct);

// YP (87)
template <Traits traits>
void State::destruct_suicides()
{
    MONAD_ASSERT(!version_);

    for (auto &it : current_) {
        auto &account_state = it.second;
        if (account_state.is_destructed()) {
            auto &account = account_state.account_;
            if constexpr (traits::evm_rev() < MONAD_ETH_CANCUN) {
                account.reset();
            }
            else {
                if (account->incarnation == incarnation_) {
                    account.reset();
                }
            }
        }
    }
}

EXPLICIT_TRAITS_MEMBER(State::destruct_suicides);

// YP (88)
void State::destruct_touched_dead()
{
    MONAD_ASSERT(!version_);
    // Every frame closed: asserted once on the journal rather than once per row on a
    // version stack that no longer exists. Stronger, too -- an unbalanced push leaves a
    // mark behind even when no row was touched.
    MONAD_ASSERT(undo_.empty() && undo_marks_.empty());

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

vm::SharedVarcode State::read_code(bytes32_t const &code_hash)
{
    {
        auto const it = code_.find(code_hash);
        if (it != code_.end()) {
            return it->second;
        }
    }
    return block_state_.read_code(code_hash);
}

vm::SharedVarcode State::get_code(Address const &address)
{
    auto const &account = recent_account(address);
    if (MONAD_UNLIKELY(!account.has_value())) {
        return block_state_.read_code(NULL_HASH);
    }
    return read_code(account.value().code_hash);
}

size_t State::get_code_size(Address const &address)
{
    auto const &account = recent_account(address);
    if (MONAD_UNLIKELY(!account.has_value())) {
        return 0;
    }
    bytes32_t const &code_hash = account.value().code_hash;
    {
        auto const it = code_.find(code_hash);
        if (it != code_.end()) {
            auto const &vcode = it->second;
            MONAD_ASSERT(vcode);
            return vcode->intercode()->size();
        }
    }
    auto const vcode = block_state_.read_code(code_hash);
    MONAD_ASSERT(vcode);
    return vcode->intercode()->size();
}

size_t State::copy_code(
    Address const &address, size_t const offset, uint8_t *const buffer,
    size_t const buffer_size)
{
    auto const &account = recent_account(address);
    if (MONAD_UNLIKELY(!account.has_value())) {
        return 0;
    }
    vm::SharedVarcode const vcode = read_code(account.value().code_hash);
    MONAD_ASSERT(vcode);
    return vcode->intercode()->copy_code(offset, buffer, buffer_size);
}

void State::set_code(Address const &address, byte_string_view const code)
{
    auto &account = current_account(address);
    if (MONAD_UNLIKELY(!account.has_value())) {
        return;
    }

    auto const code_hash = to_bytes(keccak256(code));
    code_[code_hash] = vm().try_insert_varcode_raw(code_hash, code);
    account.value().code_hash = code_hash;
    rb_.on_set_code(address, code);
}

void State::create_contract(Address const &address)
{
    auto &account = current_account(address);
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
void State::create_account_no_rollback(Address const &address)
{
    auto &account = current_account(address);
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

void State::store_log(Receipt::Log const &log)
{
    logs_.push_back(log);
}

void State::set_to_state_incarnation(Address const &address)
{
    auto &account = current_account(address);
    if (MONAD_UNLIKELY(!account.has_value())) {
        account = Account{.incarnation = incarnation_};
    }
    account.value().incarnation = incarnation_;
}

// RELAXED MERGE
// if original and current can be adjusted to satisfy min balance, adjust
// both values for merge
bool State::try_fix_account_mismatch(
    Address const &address, std::optional<Account> const &actual)
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
    Address const &address, uint256_t const &debit)
{
    auto const &account = recent_account(address);
    uint256_t const balance = account.has_value() ? account->balance : 0;

    auto &original_state = original_account_state(address);
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
}

MONAD_NAMESPACE_END
