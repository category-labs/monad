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

#include <category/core/address.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/execution/ethereum/execution_modalities.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/ethereum/validate_transaction_error.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/system_sender.hpp>
#include <category/execution/monad/validate_monad_transaction.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>

#include <algorithm>
#include <initializer_list>
#include <optional>
#include <span>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
Result<void> validate_transaction(
    Transaction const &tx, Address const &sender, State &state,
    uint256_t const &base_fee_per_gas,
    std::span<std::optional<Address> const> const authorities,
    trace::StateTracer &state_tracer, ChainContext<traits> const &ctx)
{
    if (is_domain_system_relayer(ctx, sender)) {
        // Its nonce is the hub's message nonce, and nobody can delegate it.
        return outcome::success();
    }
    if (!sender_nonce_check(ctx.mode)) {
        BOOST_OUTCOME_TRY(validate_simulation_sender_nonce(sender, state));
    }
    auto res = validate_ethereum_transaction<traits>(
        tx, sender, state, state_tracer, ctx.mode);
    if (MONAD_UNLIKELY(ctx.private_domain)) {
        // Nothing is charged on a private domain, so only value needs a
        // balance, and it has no native token to pay value with.
        // InsufficientBalance is the last check above.
        if (res.has_error() &&
            res.error() != TransactionError::InsufficientBalance) {
            return res;
        }
        if (MONAD_UNLIKELY(tx.value != 0)) {
            return TransactionError::InsufficientBalance;
        }
    }
    else if constexpr (traits::reserve_balance_active()) {
        if (res.has_error() &&
            res.error() != TransactionError::InsufficientBalance) {
            return res;
        }

        uint256_t const gas_fee =
            uint256_t{tx.gas_limit} * gas_price<traits>(tx, base_fee_per_gas);
        if (MONAD_UNLIKELY(state.get_balance(sender) < gas_fee)) {
            return MonadTransactionError::InsufficientBalanceForFee;
        }
    }
    else if (res.has_error()) {
        return res;
    }

    if constexpr (traits::staking_active()) {
        if (MONAD_UNLIKELY(std::ranges::contains(authorities, SYSTEM_SENDER))) {
            return MonadTransactionError::SystemTransactionSenderIsAuthority;
        }
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
