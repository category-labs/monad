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
#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/execution_context.hpp>

#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

BlockExecutionContext::BlockExecutionContext(
    ExecutionMode const mode, Block const &block,
    std::span<Address const> senders,
    std::span<std::vector<std::optional<Address>> const> authorities,
    std::span<std::unique_ptr<CallTracerBase>> const call_tracers,
    std::span<std::unique_ptr<trace::StateTracer>> const state_tracers,
    bool enable_native_transfer_tracing)
    : block{block}
    , senders{senders}
    , authorities{authorities}
    , mode{mode}
    , call_tracers_{call_tracers}
    , state_tracers_{state_tracers}
    , enable_native_transfer_tracing_{enable_native_transfer_tracing}
    , sliced_{block.transactions.size()}
{
    MONAD_ASSERT(block.transactions.size() == senders.size());
    MONAD_ASSERT(block.transactions.size() == authorities.size());
}

BlockExecutionContext BlockExecutionContext::normal(
    Block const &block, std::span<Address const> senders,
    std::span<std::vector<std::optional<Address>> const> authorities)
{
    return BlockExecutionContext{
        ExecutionMode::Normal, block, senders, authorities, {}, {}, false};
}

BlockExecutionContext BlockExecutionContext::call_tracing(
    Block const &block, std::span<Address const> senders,
    std::span<std::vector<std::optional<Address>> const> authorities,
    std::span<std::unique_ptr<CallTracerBase>> const call_tracers)
{
    MONAD_ASSERT(call_tracers.size() == block.transactions.size());
    return BlockExecutionContext{
        ExecutionMode::CallTracing,
        block,
        senders,
        authorities,
        call_tracers,
        {},
        false};
}

BlockExecutionContext BlockExecutionContext::state_tracing(
    Block const &block, std::span<Address const> senders,
    std::span<std::vector<std::optional<Address>> const> authorities,
    std::span<std::unique_ptr<trace::StateTracer>> const state_tracers)
{
    MONAD_ASSERT(state_tracers.size() == block.transactions.size());
    return BlockExecutionContext{
        ExecutionMode::StateTracing,
        block,
        senders,
        authorities,
        {},
        state_tracers,
        false};
}

TxExecutionContext BlockExecutionContext::operator[](uint64_t const i) const
{
    // Remove constness to allow non-const mark()
    const_cast<SliceTracker &>(sliced_).mark(i);

    if (mode == ExecutionMode::CallTracing) {
        MONAD_ASSERT(
            !call_tracers_.empty(),
            "BlockExecutionContext: CallTracing mode but call_tracers_ is "
            "empty (construction bug)");
    }

    if (mode == ExecutionMode::StateTracing) {
        MONAD_ASSERT(
            !state_tracers_.empty(),
            "BlockExecutionContext: StateTracing mode but state_tracers_ is "
            "empty (construction bug)");
    }

    return {i, this, block.transactions[i], senders[i], authorities[i]};
}

// `get_call_tracer` and `get_state_tracer` perform "delayed" slicing of the
// block execution context.
CallTracerBase &TxExecutionContext::get_call_tracer() const
{

    if (block_ctx_->mode == ExecutionMode::CallTracing) {
        return *(block_ctx_->call_tracers_[i]);
    }
    return block_ctx_->noop_call_tracer_;
}

trace::StateTracer &TxExecutionContext::get_state_tracer() const
{
    if (block_ctx_->mode == ExecutionMode::StateTracing) {
        return *(block_ctx_->state_tracers_[i]);
    }
    return block_ctx_->noop_state_tracer_;
}

bool TxExecutionContext::trace_transfers() const
{
    return block_ctx_->enable_native_transfer_tracing_;
}

ExecutionMode TxExecutionContext::mode() const
{
    return block_ctx_->mode;
}

MONAD_NAMESPACE_END
