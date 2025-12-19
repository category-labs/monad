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

#include <category/core/config.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/system_sender.hpp>
#include <category/execution/monad/validate_monad_transaction.hpp>

#include <boost/outcome/success_failure.hpp>

#include <ranges>
#include <system_error>

MONAD_NAMESPACE_BEGIN

Result<void> validate_monad_transaction(
    monad_revision const monad_rev, evmc_revision const rev,
    Transaction const &tx, Address const &sender, State &state,
    uint256_t const &base_fee_per_gas,
    std::span<std::optional<Address> const> const authorities)
{
    auto res = ::monad::validate_transaction(rev, tx, sender, state);
    if (MONAD_LIKELY(monad_rev >= MONAD_FOUR)) {
        if (res.has_error() &&
            res.error() != TransactionError::InsufficientBalance) {
            return res;
        }

        uint256_t const gas_fee =
            uint256_t{tx.gas_limit} * gas_price(rev, tx, base_fee_per_gas);
        if (MONAD_UNLIKELY(state.get_balance(sender) < gas_fee)) {
            return MonadTransactionError::InsufficientBalanceForFee;
        }

        if (MONAD_UNLIKELY(std::ranges::contains(authorities, SYSTEM_SENDER))) {
            return MonadTransactionError::SystemTransactionSenderIsAuthority;
        }
    }
    else if (monad_rev >= MONAD_ZERO) {
        return res;
    }
    else {
        MONAD_ABORT("invalid revision");
    }

    return outcome::success();
}

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::MonadTransactionError>::mapping> const &
quick_status_code_from_enum<monad::MonadTransactionError>::value_mappings()
{
    using monad::MonadTransactionError;

    static std::initializer_list<mapping> const v = {
        {MonadTransactionError::Success, "success", {errc::success}},
        {MonadTransactionError::InsufficientBalanceForFee,
         "insufficient balance for fee",
         {}},
        {MonadTransactionError::SystemTransactionSenderIsAuthority,
         "system transaction sender is authority",
         {}},
    };

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
