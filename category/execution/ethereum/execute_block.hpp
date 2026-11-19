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

#pragma once

#include <category/core/address.hpp>
#include <category/core/config.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/dispatch_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/vm/evm/traits.hpp>

#include <memory>
#include <optional>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
class BlockState;
class ExecutionEventRecorder;
class State;
struct Block;
struct Chain;

namespace fiber
{
    class FiberGroup;
    class PriorityPool;
} // namespace fiber

template <Traits traits>
Result<std::vector<Receipt>> execute_block_transactions(
    Chain const &, BlockHeader const &, std::span<Transaction const>,
    std::span<Address const> senders,
    std::span<std::vector<std::optional<Address>> const> authorities,
    BlockState &, BlockHashBuffer const &, fiber::FiberGroup &, BlockMetrics &,
    std::span<std::unique_ptr<CallTracerBase>>,
    std::span<std::unique_ptr<trace::StateTracer>> state_tracers,
    ChainContext<traits> const &chain_ctx, ExecutionEventRecorder *,
    bool trace_transfers = false);

template <Traits traits>
Result<std::vector<Receipt>> execute_block(
    Chain const &, Block const &, std::span<Address const> senders,
    std::span<std::vector<std::optional<Address>> const> authorities,
    BlockState &, BlockHashBuffer const &, fiber::FiberGroup &, BlockMetrics &,
    std::span<std::unique_ptr<CallTracerBase>>,
    std::span<std::unique_ptr<trace::StateTracer>> state_tracers,
    trace::StateTracer &system_call_state_tracer,
    ChainContext<traits> const &chain_ctx, ExecutionEventRecorder *,
    bool trace_transfers = false);

/// The signers of a block's transactions. `senders[i]` is the sender of
/// transaction `i` and `authorities[i][j]` the authority of its `j`-th EIP-7702
/// authorization entry; an element is nullopt if its signature does not
/// recover.
struct RecoveredSigners
{
    std::vector<std::optional<Address>> senders;
    std::vector<std::vector<std::optional<Address>>> authorities;
};

/// Recovers every sender and authority of `transactions`. All of their
/// signatures are pooled into one sequence and recovered in batches through
/// recover_addresses, with the batches spread over the pool's threads.
RecoveredSigners
recover_signers(std::span<Transaction const>, fiber::PriorityPool &);

MONAD_NAMESPACE_END
