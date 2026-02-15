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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/state3/version_stack.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/reserve_balance.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <evmc/evmc.h>

#include <ankerl/unordered_dense.h>

#include <immer/vector.hpp>

#include <cstddef>
#include <cstdint>
#include <deque>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

class BlockState;
struct Transaction;

class State
{
    template <typename K, typename V>
    using Map = ankerl::unordered_dense::segmented_map<K, V>;

    template <typename K>
    using Set = ankerl::unordered_dense::segmented_set<K>;

    BlockState &block_state_;

    Incarnation const incarnation_;

    Map<Address, AccountHistory> history_{};

    VersionStack<immer::vector<Receipt::Log>> logs_{{}};

    Map<bytes32_t, vm::SharedVarcode> code_{};

    unsigned version_{0};

    std::deque<Set<Address>> dirty_;

    bool const relaxed_validation_{false};
    ReserveBalance rb_;

public:
    OriginalAccountState &original_account_state(Address const &);

private:
    AccountHistory &account_history(Address const &);

    AccountState const &recent_account_state(Address const &);

    CurrentAccountState &current_account_state(Address const &);

    std::optional<Account> const &recent_account(Address const &);

    std::optional<Account> &current_account(Address const &);

    void add_to_balance(
        AccountHistory &, Address const &, uint256_t const &delta);

    void subtract_from_balance(
        AccountHistory &, Address const &, uint256_t const &delta);

public:
    State(BlockState &, Incarnation, bool relaxed_validation = false);

    State(State &&) = delete;
    State(State const &) = delete;
    State &operator=(State &&) = delete;
    State &operator=(State const &) = delete;

    Map<Address, AccountHistory> const &history() const;

    Map<bytes32_t, vm::SharedVarcode> const &code() const;

    void push();

    void pop_accept();

    void pop_reject();

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

    bytes32_t get_storage(Address const &, bytes32_t const &key);

    bytes32_t get_transient_storage(Address const &, bytes32_t const &key);

    bool is_touched(Address const &);

    ////////////////////////////////////////

    void set_nonce(Address const &, uint64_t nonce);

    void add_to_balance(Address const &, uint256_t const &delta);

    void subtract_from_balance(Address const &, uint256_t const &delta);

    void set_code_hash(Address const &, bytes32_t const &hash);

    evmc_storage_status
    set_storage(Address const &, bytes32_t const &key, bytes32_t const &value);

    void set_transient_storage(
        Address const &, bytes32_t const &key, bytes32_t const &value);

    void touch(Address const &);

    evmc_access_status access_account(Address const &);

    evmc_access_status access_storage(Address const &, bytes32_t const &key);

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

    [[nodiscard]] bool reserve_balance_tracking_enabled() const;
    [[nodiscard]] bool reserve_balance_has_violation() const;

    bool is_delegated(bytes32_t const &code_hash);

    ////////////////////////////////////////

    immer::vector<Receipt::Log> const &logs();

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

    template <Traits traits>
    void init_reserve_balance_context(
        Address const &sender, Transaction const &tx,
        std::optional<uint256_t> const &base_fee_per_gas, uint64_t i,
        ChainContext<traits> const &ctx)
    {
        rb_.init_from_tx<traits>(sender, tx, base_fee_per_gas, i, ctx);
    }
};

MONAD_NAMESPACE_END
