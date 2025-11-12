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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/state3/version_stack.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/vm/code.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <evmc/evmc.h>

#include <intx/intx.hpp>

#include <immer/vector.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

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
        return it->second.recent();
    }
    // original
    return original_account_state(address);
}

AccountState &State::current_account_state(Address const &address)
{
    // current
    auto it = current_.find(address);
    if (MONAD_UNLIKELY(it == current_.end())) {
        // original
        auto const &account_state = original_account_state(address);
        it = current_.try_emplace(address, account_state, version_).first;
    }
    if (!dirty_.empty()) {
        dirty_.back().emplace(address);
    }
    return it->second.current(version_);
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
{
}

State::Map<Address, OriginalAccountState> const &State::original() const
{
    return original_;
}

State::Map<Address, OriginalAccountState> &State::original()
{
    return original_;
}

State::Map<Address, VersionStack<AccountState>> const &State::current() const
{
    return current_;
}

State::Map<bytes32_t, vm::SharedVarcode> const &State::code() const
{
    return code_;
}

void State::push()
{
    MONAD_ASSERT(dirty_.size() == version_);

    ++version_;
    dirty_.emplace_back();
}

void State::pop_accept()
{
    MONAD_ASSERT(version_);
    MONAD_ASSERT(dirty_.size() == version_);

    auto accounts = std::move(dirty_.back());
    dirty_.pop_back();
    for (auto const &dirty_address : accounts) {
        auto const it = current_.find(dirty_address);
        MONAD_ASSERT(it != current_.end());
        it->second.pop_accept(version_);
        if (!dirty_.empty()) {
            dirty_.back().emplace(dirty_address);
        }
    }

    logs_.pop_accept(version_);

    --version_;
}

void State::pop_reject()
{
    MONAD_ASSERT(version_);
    MONAD_ASSERT(dirty_.size() == version_);

    std::vector<Address> removals;
    auto accounts = std::move(dirty_.back());
    dirty_.pop_back();
    for (auto const &dirty_address : accounts) {
        auto const it = current_.find(dirty_address);
        MONAD_ASSERT(it != current_.end());
        if (it->second.pop_reject(version_)) {
            removals.push_back(it->first);
        }
    }

    logs_.pop_reject(version_);

    while (removals.size()) {
        current_.erase(removals.back());
        removals.pop_back();
    }

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

bytes32_t State::get_current_balance_pessimistic(Address const &address)
{
    auto const &account = recent_account(address);
    original_account_state(address).set_validate_exact_balance();
    if (MONAD_LIKELY(account.has_value())) {
        return intx::be::store<bytes32_t>(account.value().balance);
    }
    return {};
}

bytes32_t State::get_original_balance_pessimistic(Address const &address)
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

bytes32_t State::get_storage(Address const &address, bytes32_t const &key)
{
    auto const it = current_.find(address);
    if (it == current_.end()) {
        auto const it2 = original_.find(address);
        MONAD_ASSERT(it2 != original_.end());
        auto &account_state = it2->second;
        auto const &account = account_state.account_;
        MONAD_ASSERT(account.has_value());
        auto &storage = account_state.storage_;
        auto const *const it3 = storage.find(key);
        if (!it3) {
            bytes32_t const value = block_state_.read_storage(
                address, account.value().incarnation, key);
            storage = storage.insert({key, value});
            return value;
        }
        else {
            return *it3;
        }
    }
    else {
        auto const &account_state = it->second.recent();
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
        auto const *const it3 = original_storage.find(key);
        if (!it3) {
            bytes32_t const value = block_state_.read_storage(
                address, account.value().incarnation, key);
            original_storage = original_storage.insert({key, value});
            return value;
        }
        else {
            return *it3;
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
    auto const &account_state = recent_account_state(address);
    return account_state.is_touched();
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
}

void State::set_code_hash(Address const &address, bytes32_t const &hash)
{
    auto &account = current_account(address);
    MONAD_ASSERT(account.has_value());
    account.value().code_hash = hash;
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
        auto const *it = storage.find(key);
        if (it == nullptr) {
            Incarnation const incarnation = account_state.account_->incarnation;
            bytes32_t const value =
                block_state_.read_storage(address, incarnation, key);
            storage = storage.insert({key, value});
            original_value = value;
        }
        else {
            original_value = *it;
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

evmc_access_status
State::access_storage(Address const &address, bytes32_t const &key)
{
    auto &account_state = current_account_state(address);
    return account_state.access_storage(key);
}

template <Traits traits>
bool State::selfdestruct(Address const &address, Address const &beneficiary)
{
    auto &account_state = current_account_state(address);
    auto &account = account_state.account_;
    MONAD_ASSERT(account.has_value());

    if constexpr (traits::evm_rev() < EVMC_CANCUN) {
        add_to_balance(beneficiary, account.value().balance);
        account.value().balance = 0;
        original_account_state(address).set_validate_exact_balance();
    }
    else {
        if (address != beneficiary || account->incarnation == incarnation_) {
            add_to_balance(beneficiary, account.value().balance);
            account.value().balance = 0;
            original_account_state(address).set_validate_exact_balance();
        }
    }

    return account_state.destruct();
}

EXPLICIT_TRAITS_MEMBER(State::selfdestruct);

// YP (87)
template <Traits traits>
void State::destruct_suicides()
{
    MONAD_ASSERT(!version_);

    for (auto &it : current_) {
        auto &stack = it.second;
        MONAD_ASSERT(stack.size() == 1);
        MONAD_ASSERT(stack.version() == 0);
        auto &account_state = stack.current(0);
        if (account_state.is_destructed()) {
            auto &account = account_state.account_;
            if constexpr (traits::evm_rev() < EVMC_CANCUN) {
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

    for (auto &it : current_) {
        auto &stack = it.second;
        MONAD_ASSERT(stack.size() == 1);
        MONAD_ASSERT(stack.version() == 0);
        auto &account_state = stack.current(0);
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
    bytes32_t const &code_hash = account.value().code_hash;
    vm::SharedVarcode vcode{};
    {
        auto const it = code_.find(code_hash);
        if (it != code_.end()) {
            vcode = it->second;
        }
        else {
            vcode = block_state_.read_code(code_hash);
        }
    }
    MONAD_ASSERT(vcode);
    auto const &icode = vcode->intercode();
    auto const code_size = icode->size();
    if (offset > code_size) {
        return 0;
    }
    auto const n = std::min(code_size - offset, buffer_size);
    std::copy_n(icode->code() + offset, n, buffer);
    return n;
}

void State::set_code(Address const &address, byte_string_view const code)
{
    auto &account = current_account(address);
    if (MONAD_UNLIKELY(!account.has_value())) {
        return;
    }

    auto const code_hash = to_bytes(keccak256(code));
    code_[code_hash] =
        vm().try_insert_varcode(code_hash, vm::make_shared_intercode(code));
    account.value().code_hash = code_hash;
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

immer::vector<Receipt::Log> const &State::logs()
{
    return logs_.recent();
}

void State::store_log(Receipt::Log const &log)
{
    auto &logs = logs_.current(version_);
    logs = logs.push_back(log);
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
    Address const &address, OriginalAccountState &original_state,
    std::optional<Account> const &actual)
{
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
    auto it = current_.find(address);
    if (it != current_.end()) {
        MONAD_ASSERT(it->second.size() == 1);
        auto &recent_state = it->second.recent();
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
