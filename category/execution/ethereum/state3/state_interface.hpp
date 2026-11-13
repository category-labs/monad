// Copyright (C) 2025-26 Category Labs, Inc.
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
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/vm/code.hpp>
#include <category/vm/evm/access_status.hpp>
#include <category/vm/evm/storage_status.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <concepts>
#include <cstddef>
#include <cstdint>
#include <ranges>
#include <utility>

MONAD_NAMESPACE_BEGIN

enum class SelfdestructRule
{
    // Every destructed account is deleted (before EIP-6780).
    DeleteAll,
    // Only an account created in this transaction is deleted (EIP-6780).
    DeleteCreatedInTransaction,
    // An account created in this transaction keeps its balance but loses its
    // nonce, code and storage, and is deleted if that leaves it empty
    // (EIP-8246).
    ClearCreatedInTransaction,
};

// The logs a backend hands back: a range whose elements build receipts.
template <class R>
concept LogRange = std::ranges::input_range<R> &&
                   std::convertible_to<
                       std::ranges::range_reference_t<R>, Receipt::Log const &>;

/**
 * The state contract seen by transaction execution, the EVM host, the
 * precompiles and the block prologue. Execution code is written against this
 * surface and nothing else.
 *
 * Container accessors such as original() and current() are deliberately not
 * part of the contract. They expose a backend's internal layout and are only
 * read by tracers and event recorders, which a backend may not support.
 */
template <class S>
concept StateInterface = requires(
    S s, Address const &address, bytes32_t const &key, bytes32_t const &value,
    uint64_t const nonce, uint256_t const &amount, byte_string_view const code,
    uint8_t *const buffer, size_t const n, Receipt::Log const &log) {
    // call frames
    { s.push() } -> std::same_as<void>;
    { s.pop_accept() } -> std::same_as<void>;
    { s.pop_reject() } -> std::same_as<void>;
    { s.vm() } -> std::same_as<vm::VM &>;

    // account reads
    { s.account_exists(address) } -> std::same_as<bool>;
    { s.account_is_dead(address) } -> std::same_as<bool>;
    { s.account_has_code_or_nonce(address) } -> std::same_as<bool>;
    { s.get_nonce(address) } -> std::same_as<uint64_t>;
    { s.get_balance(address) } -> std::same_as<uint256_t>;
    { s.get_code_hash(address) } -> std::same_as<bytes32_t>;
    { s.is_destructed(address) } -> std::same_as<bool>;
    { s.is_current_incarnation(address) } -> std::same_as<bool>;
    { s.is_touched(address) } -> std::same_as<bool>;
    {
        s.record_balance_constraint_for_debit(address, amount)
    } -> std::same_as<bool>;

    // account writes
    { s.set_nonce(address, nonce) } -> std::same_as<void>;
    { s.add_to_balance(address, amount) } -> std::same_as<void>;
    { s.subtract_from_balance(address, amount) } -> std::same_as<void>;
    { s.touch(address) } -> std::same_as<void>;
    { s.create_contract(address) } -> std::same_as<void>;
    { s.create_account_no_rollback(address) } -> std::same_as<void>;
    { s.set_to_state_incarnation(address) } -> std::same_as<void>;
    { s.destruct_touched_dead() } -> std::same_as<void>;

    // storage and warmth
    { s.get_storage(address, key) } -> std::same_as<bytes32_t>;
    { s.set_storage(address, key, value) } -> std::same_as<StorageStatus>;
    { s.get_transient_storage(address, key) } -> std::same_as<bytes32_t>;
    { s.set_transient_storage(address, key, value) } -> std::same_as<void>;
    { s.access_account(address) } -> std::same_as<AccessStatus>;

    // code
    { s.read_code(key) } -> std::same_as<vm::SharedVarcode>;
    { s.get_code(address) } -> std::same_as<vm::SharedVarcode>;
    { s.get_code_size(address) } -> std::same_as<size_t>;
    { s.copy_code(address, n, buffer, n) } -> std::same_as<size_t>;
    { s.set_code(address, code) } -> std::same_as<void>;

    // logs
    { s.logs() } -> LogRange;
    { s.store_log(log) } -> std::same_as<void>;
};

template <Traits traits>
consteval SelfdestructRule selfdestruct_rule()
{
    static_assert(
        !traits::eip_8246_active() || traits::eip_6780_active(),
        "EIP-8246 implies EIP-6780");
    if constexpr (!traits::eip_6780_active()) {
        return SelfdestructRule::DeleteAll;
    }
    else if constexpr (!traits::eip_8246_active()) {
        return SelfdestructRule::DeleteCreatedInTransaction;
    }
    else {
        return SelfdestructRule::ClearCreatedInTransaction;
    }
}

template <class Derived>
class StateBase
{
    friend Derived;

    StateBase() = default;

    Derived &derived()
    {
        return static_cast<Derived &>(*this);
    }

public:
    bool account_exists(Address const &address)
    {
        return derived().recent_account(address).has_value();
    }

    bool account_is_dead(Address const &address)
    {
        return is_dead(derived().recent_account(address));
    }

    bool account_has_code_or_nonce(Address const &address)
    {
        auto const &account = derived().recent_account(address);
        if (!account.has_value()) {
            return false;
        }

        auto const &account_val = account.value();
        return account_val.nonce > 0 || account_val.code_hash != NULL_HASH;
    }

    uint64_t get_nonce(Address const &address)
    {
        auto const &account = derived().recent_account(address);
        if (MONAD_LIKELY(account.has_value())) {
            return account.value().nonce;
        }
        return 0;
    }

    bytes32_t get_code_hash(Address const &address)
    {
        auto const &account = derived().recent_account(address);
        if (MONAD_LIKELY(account.has_value())) {
            return account.value().code_hash;
        }
        return NULL_HASH;
    }

    template <Traits traits>
    AccessStatus access_storage(Address const &address, bytes32_t const &key)
    {
        return derived().template access_storage_impl<traits::mip_8_active()>(
            address, key);
    }

    template <Traits traits>
    std::pair<bool, uint256_t>
    selfdestruct(Address const &address, Address const &beneficiary)
    {
        return derived()
            .template selfdestruct_impl<selfdestruct_rule<traits>()>(
                address, beneficiary);
    }

    // YP (87)
    template <Traits traits>
    void destruct_suicides()
    {
        derived()
            .template destruct_suicides_impl<selfdestruct_rule<traits>()>();
    }
};

MONAD_NAMESPACE_END
