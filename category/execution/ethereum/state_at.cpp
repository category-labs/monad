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
#include <category/execution/ethereum/metrics/block_metrics.hpp>
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
    std::vector<Transaction> const &transactions,
    std::vector<Address> const &senders,
    std::vector<std::vector<std::optional<Address>>> const &authorities,
    BlockState &block_state, BlockHashBuffer const &block_hash_buffer,
    fiber::PriorityPool &fiber_pool,
    std::vector<std::unique_ptr<trace::StateTracer>> &state_tracers)
{
    MONAD_ASSERT(transactions.size() == senders.size());
    MONAD_ASSERT(transactions.size() == authorities.size());
    MONAD_ASSERT(transactions.size() == state_tracers.size());

    std::vector<std::unique_ptr<CallTracerBase>> noop_call_tracers{};
    noop_call_tracers.reserve(transactions.size());

    for (size_t i = 0; i < transactions.size(); ++i) {
        noop_call_tracers.emplace_back(std::unique_ptr<NoopCallTracer>{
            std::make_unique<NoopCallTracer>()});
    }
    MONAD_ASSERT(noop_call_tracers.size() == transactions.size());

    // TODO(dhil): Probably worth being able to replay up
    // to a bound.

    // preprocess block
    BlockMetrics metrics{};
    Result<std::vector<Receipt>> result = execute_block_transactions<traits>(
        chain,
        header,
        transactions,
        senders,
        authorities,
        block_state,
        block_hash_buffer,
        fiber_pool,
        metrics,
        noop_call_tracers,
        state_tracers);
    (void)result;

    // State state{block_state, Incarnation{0, Incarnation::LAST_TX}};
    // MONAD_ASSERT(block_state.can_merge(state));
    // block_state.merge(state);
}

EXPLICIT_TRAITS(state_after_transactions)
MONAD_NAMESPACE_END
