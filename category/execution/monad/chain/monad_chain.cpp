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
#include <category/core/result.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/chain/validate_monad_transaction.hpp>
#include <category/execution/monad/monad_precompiles.hpp>
#include <category/execution/monad/reserve_balance.h>
#include <category/execution/monad/reserve_balance.hpp>
#include <category/execution/monad/system_sender.hpp>
#include <category/vm/evm/switch_traits.hpp>

#include <ranges>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

evmc_revision MonadChain::get_revision(
    uint64_t /*block_number*/, uint64_t const timestamp) const
{
    auto const monad_revision = get_monad_revision(timestamp);

    if (MONAD_LIKELY(monad_revision >= MONAD_FOUR)) {
        return EVMC_PRAGUE;
    }

    return EVMC_CANCUN;
}

Result<void> MonadChain::validate_output_header(
    BlockHeader const &input, BlockHeader const &output) const
{
    if (MONAD_UNLIKELY(input.ommers_hash != output.ommers_hash)) {
        return BlockError::WrongOmmersHash;
    }
    if (MONAD_UNLIKELY(input.transactions_root != output.transactions_root)) {
        return BlockError::WrongMerkleRoot;
    }
    if (MONAD_UNLIKELY(input.withdrawals_root != output.withdrawals_root)) {
        return BlockError::WrongMerkleRoot;
    }

    // YP eq. 56
    if (MONAD_UNLIKELY(output.gas_used > output.gas_limit)) {
        return BlockError::GasAboveLimit;
    }
    return success();
}

Result<void> MonadChain::validate_transaction(
    uint64_t const block_number, uint64_t const timestamp,
    Transaction const &tx, Address const &sender, State &state,
    uint256_t const &base_fee_per_gas,
    std::vector<std::optional<Address>> const &authorities) const
{
    evmc_revision const rev = get_revision(block_number, timestamp);
    auto const acct = state.recent_account(sender);
    auto const &icode = state.get_code(sender)->intercode();
    auto res = ::monad::validate_transaction(
        rev, tx, acct, {icode->code(), icode->size()});
    auto const monad_rev = get_monad_revision(timestamp);
    if (MONAD_LIKELY(monad_rev >= MONAD_FOUR)) {
        if (res.has_error() &&
            res.error() != TransactionError::InsufficientBalance) {
            return res;
        }

        evmc_revision const rev = get_revision(block_number, timestamp);
        uint256_t const balance = acct.has_value() ? acct.value().balance : 0;
        uint256_t const gas_fee =
            uint256_t{tx.gas_limit} * gas_price(rev, tx, base_fee_per_gas);
        if (MONAD_UNLIKELY(balance < gas_fee)) {
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
    return success();
}

bool MonadChain::revert_transaction(
    uint64_t const block_number, uint64_t const timestamp,
    Address const &sender, Transaction const &tx,
    uint256_t const &base_fee_per_gas, uint64_t const i, State &state,
    MonadChainContext const &ctx) const
{
    monad_revision const monad_rev = get_monad_revision(timestamp);
    evmc_revision const rev = get_revision(block_number, timestamp);
    return revert_monad_transaction(
        monad_rev, rev, sender, tx, base_fee_per_gas, i, state, ctx);
}

MONAD_NAMESPACE_END
