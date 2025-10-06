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

#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/state_at.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <evmc/evmc.hpp>
#include <nlohmann/json.hpp>

#include <iterator>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
void state_after_transactions(
    Chain const &chain, BlockHeader const &header,
    BlockHashBuffer const &buffer, CallTracerBase &call_tracer,
    trace::StateTracer &state_tracer, BlockState &block_state,
    std::vector<std::optional<Address>> const &senders,
    std::vector<std::vector<std::optional<Address>>> const &authorities,
    std::vector<Transaction> const
        &txns) // TODO(dhil): Probably worth being able to replay up to a bound.
{
    MONAD_ASSERT(txns.size() == senders.size());
    MONAD_ASSERT(txns.size() == authorities.size());

    for (size_t i = 0; i < txns.size(); ++i) {
        Transaction const txn = txns[i];
        Address const sender = [&senders, i]() -> Address {
            if (senders[i].has_value()) {
                return *senders[i];
            }
            // TODO(dhil): any possible "default" sender?
            MONAD_ABORT("Failed to recover sender");
        }();
        ExecuteTransactionNoValidation<traits> execute_tx(
            chain, txn, sender, authorities[i], header, i);
        State state{
            block_state, Incarnation{header.number, static_cast<uint64_t>(i)}};
        evmc_tx_context tx_context =
            get_tx_context<traits>(txn, sender, header, chain.get_chain_id());
        EvmcHost<traits> host{chain, call_tracer, tx_context, buffer, state};
        evmc::Result result = execute_tx(state, host);
        if (result.status_code != EVMC_SUCCESS &&
            result.status_code != EVMC_REVERT) {
            // TODO(dhil): proper error handling
            MONAD_ABORT("Transaction execution failed");
        }
        trace::run_tracer(
            state_tracer, state); // TODO(dhil): glue state traces together
        MONAD_ASSERT(block_state.can_merge(state));
        block_state.merge(state);
    }
}

EXPLICIT_TRAITS(state_after_transactions)
MONAD_NAMESPACE_END
