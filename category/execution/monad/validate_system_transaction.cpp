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

#include <category/core/likely.h>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/execution/monad/system_sender.hpp>
#include <category/execution/monad/validate_system_transaction.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <boost/outcome/config.hpp>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/generic_code.hpp>
#endif

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

template <Traits traits>
Result<void>
static_validate_system_transaction(Transaction const &tx, Address const &sender)
{
    if constexpr (traits::monad_rev() < MONAD_FOUR) {
        return SystemTransactionError::SystemTxnBeforeFork;
    }

    if (MONAD_UNLIKELY(sender != SYSTEM_SENDER)) {
        return SystemTransactionError::BadSender;
    }

    if (MONAD_UNLIKELY(tx.type != TransactionType::legacy)) {
        return SystemTransactionError::TypeNotLegacy;
    }

    if (MONAD_UNLIKELY(!tx.to.has_value())) {
        return SystemTransactionError::MissingTo;
    }

    if (MONAD_UNLIKELY(tx.to != staking::STAKING_CA)) {
        return SystemTransactionError::InvalidSystemContract;
    }

    if (MONAD_UNLIKELY(tx.gas_limit != 0)) {
        return SystemTransactionError::GasNonZero;
    }

    if (MONAD_UNLIKELY(tx.max_fee_per_gas != 0)) {
        return SystemTransactionError::GasNonZero;
    }

    if (MONAD_UNLIKELY(tx.max_priority_fee_per_gas != 0)) {
        return SystemTransactionError::GasNonZero;
    }

    if (MONAD_UNLIKELY(!tx.authorization_list.empty())) {
        return SystemTransactionError::NonEmptyAuthorizationList;
    }

    return success();
}

EXPLICIT_MONAD_TRAITS(static_validate_system_transaction)

Result<void> validate_system_transaction(
    Transaction const &tx, Address const &sender, State &state)
{
    if (MONAD_UNLIKELY(!state.account_exists(sender))) {
        // YP (71)
        if (tx.nonce) {
            return TransactionError::BadNonce;
        }
        return success();
    }

    // YP (71)
    if (MONAD_UNLIKELY(state.get_nonce(sender) != tx.nonce)) {
        return TransactionError::BadNonce;
    }
    return success();
}

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::SystemTransactionError>::mapping> const &
quick_status_code_from_enum<monad::SystemTransactionError>::value_mappings()
{
    using monad::SystemTransactionError;

    static std::initializer_list<mapping> const v = {
        {SystemTransactionError::Success, "success", {errc::success}},
        {SystemTransactionError::SystemTxnBeforeFork,
         "system transaction before fork",
         {}},
        {SystemTransactionError::GasNonZero, "gas non zero", {}},
        {SystemTransactionError::TypeNotLegacy, "type not legacy", {}},
        {SystemTransactionError::BadSender, "bad sender", {}},
        {SystemTransactionError::MissingTo, "missing to", {}},
        {SystemTransactionError::InvalidSystemContract,
         "invalid system contract",
         {}},
        {SystemTransactionError::NonEmptyAuthorizationList,
         "non empty authorization list",
         {}},
    };

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
