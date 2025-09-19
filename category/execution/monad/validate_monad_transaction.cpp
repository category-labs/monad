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
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/chain/monad_transaction_error.hpp>
#include <category/execution/monad/system_sender.hpp>
#include <category/execution/monad/validate_monad_transaction.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <boost/outcome/success_failure.hpp>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
Result<void> validate_transaction(
    Transaction const &tx, Address const &sender, State &state,
    uint256_t const &base_fee_per_gas,
    std::vector<std::optional<Address>> const &authorities)
{
    auto const acct = state.recent_account(sender);
    auto const &icode = state.get_code(sender)->intercode();
    auto res = validate_transaction_base<EvmTraits<traits::evm_rev()>>(
        tx, acct, {icode->code(), icode->size()});
    if constexpr (traits::monad_rev() >= MONAD_FOUR) {
        if (res.has_error() &&
            res.error() != TransactionError::InsufficientBalance) {
            return res;
        }

        uint256_t const balance = acct.has_value() ? acct.value().balance : 0;
        uint256_t const gas_fee =
            uint256_t{tx.gas_limit} * gas_price<traits>(tx, base_fee_per_gas);
        if (MONAD_UNLIKELY(balance < gas_fee)) {
            return MonadTransactionError::InsufficientBalanceForFee;
        }

        if (MONAD_UNLIKELY(std::ranges::contains(authorities, SYSTEM_SENDER))) {
            return MonadTransactionError::SystemTransactionSenderIsAuthority;
        }
    }
    else if constexpr (traits::monad_rev() >= MONAD_ZERO) {
        return res;
    }
    else {
        MONAD_ABORT("invalid revision");
    }
    return boost::outcome_v2::success();
}

EXPLICIT_MONAD_TRAITS(validate_transaction);

MONAD_NAMESPACE_END
