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
#include <category/vm/evm/explicit_traits.hpp>

#include <evmc/evmc.hpp>
#include <nlohmann/json.hpp>

#include <iterator>

MONAD_NAMESPACE_BEGIN

template <Traits traits, typename It>
void state_after_transactions(
    Chain const &chain, BlockHeader const &header,
    BlockHashBuffer const &buffer, CallTracerBase &call_tracer,
    trace::StateTracer &state_tracer, BlockState &block_state,
    std::vector<std::optional<Address>> const &senders,
    std::vector<std::vector<std::optional<Address>>> const &authorities,
    It const begin, It const end)
{
    for (auto it = begin; it != end; ++it) {
        size_t const index = std::distance(begin, it);
        Transaction const txn = *it;
        Address const sender = [&senders, index]() {
            if (senders[index].has_value()) {
                return *senders[index];
            }
            // TODO(dhil): any possible "default" sender?
            MONAD_ABORT("Failed to recover sender");
        }();
        ExecuteTransactionNoValidation<traits> execute_tx(
            chain, txn, sender, authorities[index], header, index);
        State state{
            block_state,
            Incarnation{header.number, static_cast<uint64_t>(index)}};
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

template <Traits traits>
void state_after_transactions(
    Chain const &chain, BlockHeader const &header,
    BlockHashBuffer const &buffer, CallTracerBase &call_tracer,
    trace::StateTracer &state_tracer, BlockState &bs,
    std::vector<Transaction> const &txns, fiber::PriorityPool &priority_pool)
{
    std::vector<std::optional<Address>> senders =
        recover_senders(txns, priority_pool);
    std::vector<std::vector<std::optional<Address>>> authorities =
        recover_authorities(txns, priority_pool);

    using it = std::vector<Transaction>::const_iterator;
    state_after_transactions<traits, it>(
        chain,
        header,
        buffer,
        call_tracer,
        state_tracer,
        bs,
        senders,
        authorities,
        txns.begin(),
        txns.end());
}

EXPLICIT_EVM_TRAITS(state_after_transactions)
EXPLICIT_MONAD_TRAITS(state_after_transactions)

MONAD_NAMESPACE_END
