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
#include <category/vm/evm/explicit_traits.hpp>

#include <boost/outcome/success_failure.hpp>

#include <ranges>
#include <system_error>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
Result<void> validate_transaction(
    Transaction const &tx, Address const &sender, State &state,
    uint256_t const &base_fee_per_gas,
    std::span<std::optional<Address> const> const authorities)
{
    auto res = validate_ethereum_transaction<traits>(tx, sender, state);
    if constexpr (traits::monad_rev() >= MONAD_FOUR) {
        if (res.has_error() &&
            res.error() != TransactionError::InsufficientBalance) {
            return res;
        }

        uint256_t const gas_fee =
            uint256_t{tx.gas_limit} * gas_price<traits>(tx, base_fee_per_gas);
        if (MONAD_UNLIKELY(state.get_balance(sender) < gas_fee)) {
            return MonadTransactionError::InsufficientBalanceForFee;
        }

        if (MONAD_UNLIKELY(std::ranges::contains(authorities, SYSTEM_SENDER))) {
            return MonadTransactionError::SystemTransactionSenderIsAuthority;
        }
    }
    else {
        return res;
    }
    return outcome::success();
}

EXPLICIT_MONAD_TRAITS(validate_transaction);

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
