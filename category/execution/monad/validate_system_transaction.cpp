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
#include <category/execution/monad/validate_system_transaction.hpp>

#include <silkpre/secp256k1n.hpp>

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

Result<void>
static_validate_system_transaction(Transaction const &tx, Address const &sender)
{
    if (MONAD_UNLIKELY(sender != SYSTEM_TRANSACTION_SENDER)) {
        return SystemTransactionError::BadSender;
    }

    if (MONAD_UNLIKELY(!tx.to.has_value())) {
        return SystemTransactionError::MissingTo;
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

    // TODO: change when staking is merged
    return SystemTransactionError::InvalidSystemContract;
}

Result<void> validate_system_transaction(
    Transaction const &tx, std::optional<Account> const &sender_account)
{
    if (MONAD_UNLIKELY(!sender_account.has_value())) {
        // YP (71)
        if (tx.nonce) {
            return TransactionError::BadNonce;
        }
        return success();
    }

    // YP (71)
    if (MONAD_UNLIKELY(sender_account->nonce != tx.nonce)) {
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
        {SystemTransactionError::GasNonZero, "gas non zero", {}},
        {SystemTransactionError::ValueNonZero, "value nonzero", {}},
        {SystemTransactionError::BadSender, "bad sender", {}},
        {SystemTransactionError::MissingTo, "missing to", {}},
        {SystemTransactionError::InvalidSystemContract,
         "invalid system contract",
         {}},
    };

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
