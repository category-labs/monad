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
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/dispatch_transaction.hpp>
#include <category/execution/monad/execute_system_transaction.hpp>
#include <category/execution/monad/system_sender.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <cstdint>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
Result<Receipt> dispatch_transaction(
    Chain const &chain, uint64_t const i, Transaction const &transaction,
    Address const &sender,
    std::vector<std::optional<Address>> const &authorities,
    BlockHeader const &header, BlockHashBuffer const &block_hash_buffer,
    BlockState &block_state, BlockMetrics &block_metrics,
    boost::fibers::future<void> &prev, CallTracerBase &call_tracer,
    trace::StateTracer &state_tracer, ChainContext<traits> const &chain_ctx,
    ExecutionEventRecorder *const exec_recorder, bool const trace_transfers)
{
    if (MONAD_UNLIKELY(chain_ctx.private_domain)) {
        // Deliveries come from DOMAIN_SYSTEM_RELAYER, the L1 system sender,
        // but are ordinary calls to the spoke. A transaction that fails
        // validation stays in the block with a status-0 receipt, so that the
        // block's body does not depend on execution.
        auto result = ExecuteTransaction<traits>{
            chain,
            i,
            transaction,
            sender,
            authorities,
            header,
            block_hash_buffer,
            block_state,
            block_metrics,
            prev,
            call_tracer,
            state_tracer,
            chain_ctx,
            exec_recorder,
            trace_transfers}();
        if (result.has_error()) {
            return Receipt{
                .status = 0, .gas_used = 0, .type = transaction.type};
        }
        return result;
    }
    if (traits::staking_active() && sender == SYSTEM_SENDER) {
        // System transactions is a concept used in Monad for consensus to
        // communicate state changes to execution this code handles these in a
        // separate executor.
        return ExecuteSystemTransaction<traits>{
            chain,
            i,
            transaction,
            sender,
            header,
            block_state,
            block_metrics,
            prev,
            call_tracer,
            state_tracer,
            exec_recorder}();
    }
    else {
        return ExecuteTransaction<traits>{
            chain,
            i,
            transaction,
            sender,
            authorities,
            header,
            block_hash_buffer,
            block_state,
            block_metrics,
            prev,
            call_tracer,
            state_tracer,
            chain_ctx,
            exec_recorder,
            trace_transfers}();
    }
}

EXPLICIT_MONAD_TRAITS(dispatch_transaction)

MONAD_NAMESPACE_END
