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

#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_transaction_error.hpp>
#include <category/vm/code.hpp>
#include <category/vm/evm/delegation.hpp>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>

#include <boost/outcome/config.hpp>
#include <boost/outcome/success_failure.hpp>

#include <initializer_list>
#include <optional>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
Result<void> static_validate_transaction(
    Transaction const &, std::optional<uint256_t> const &base_fee_per_gas,
    std::optional<uint64_t> const &excess_blob_gas, uint256_t const &chain_id);

template <Traits traits>
Result<void> validate_transaction(
    Transaction const &tx, Address const &sender, State &state,
    uint256_t const &base_fee_per_gas,
    std::span<std::optional<Address> const> const authorities);

template <Traits traits>
[[gnu::always_inline]] inline Result<void> validate_ethereum_transaction(
    Transaction const &tx, Address const &sender, State &state)
{
    using BOOST_OUTCOME_V2_NAMESPACE::success;

    // YP (70)
    uint512_t v0 = tx.value + max_gas_cost(tx.gas_limit, tx.max_fee_per_gas);
    if (tx.type == TransactionType::eip4844) {
        v0 += tx.max_fee_per_blob_gas * get_total_blob_gas(tx);
    }

    if (MONAD_UNLIKELY(!state.account_exists(sender))) {
        // YP (71)
        if (tx.nonce) {
            return TransactionError::BadNonce;
        }
        // YP (71)
        if (v0) {
            return TransactionError::InsufficientBalance;
        }
        return success();
    }

    // YP (71)
    bool sender_is_eoa = state.get_code_hash(sender) == NULL_HASH;
    if constexpr (traits::evm_rev() >= EVMC_PRAGUE) {
        // EIP-7702
        auto const icode = state.get_code(sender)->intercode();
        sender_is_eoa = sender_is_eoa ||
                        vm::evm::is_delegated({icode->code(), icode->size()});
    }

    if (MONAD_UNLIKELY(!sender_is_eoa)) {
        return TransactionError::SenderNotEoa;
    }

    // YP (71)
    if (MONAD_UNLIKELY(state.get_nonce(sender) != tx.nonce)) {
        return TransactionError::BadNonce;
    }

    // YP (71)
    // RELAXED MERGE
    // note this passes because `v0` includes gas which is later deducted in
    // `irrevocable_change` before relaxed merge logic in `sender_has_balance`
    // this is fragile as it depends on values in two locations matching
    if (MONAD_UNLIKELY(state.get_balance(sender) < v0)) {
        return TransactionError::InsufficientBalance;
    }

    // Note: Tg <= B_Hl - l(B_R)u can only be checked before retirement
    // (It requires knowing the parent block)

    return success();
}

MONAD_NAMESPACE_END
