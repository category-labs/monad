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

#include <category/execution/ethereum/execution_context.hpp>

#include <category/core/assert.h>
#include <category/core/config.hpp>

MONAD_NAMESPACE_BEGIN

BlockExecutionContext::BlockExecutionContext(
    ExecutionMode const mode, size_t const size,
    std::span<std::unique_ptr<CallTracerBase>> const call_tracers,
    std::span<std::unique_ptr<trace::StateTracer>> const state_tracers,
    bool enable_native_transfer_tracing)
    : mode_{mode}
    , call_tracers_{call_tracers}
    , state_tracers_{state_tracers}
    , enable_native_transfer_tracing_{enable_native_transfer_tracing}
    , sliced_{size}
{
}

BlockExecutionContext BlockExecutionContext::normal(size_t size)
{
    return BlockExecutionContext{ExecutionMode::Normal, size, {}, {}};
}

BlockExecutionContext BlockExecutionContext::call_tracing(
    size_t size, std::span<std::unique_ptr<CallTracerBase>> const call_tracers)
{
    MONAD_ASSERT(call_tracers.size() == size);
    return BlockExecutionContext{
        ExecutionMode::Tracing, size, call_tracers, {}};
}

BlockExecutionContext BlockExecutionContext::state_tracing(
    size_t size,
    std::span<std::unique_ptr<trace::StateTracer>> const state_tracers)
{
    MONAD_ASSERT(state_tracers.size() == size);
    return BlockExecutionContext{
        ExecutionMode::Tracing, size, {}, state_tracers};
}

BlockExecutionContext BlockExecutionContext::simulation(
    size_t size, std::span<std::unique_ptr<CallTracerBase>> const call_tracers,
    std::span<std::unique_ptr<trace::StateTracer>> const state_tracers,
    bool enable_native_transfer_tracing)
{
    MONAD_ASSERT(call_tracers.size() == size);
    MONAD_ASSERT(state_tracers.size() == size);
    return BlockExecutionContext{
        ExecutionMode::Simulation,
        size,
        call_tracers,
        state_tracers,
        enable_native_transfer_tracing};
}

TxExecutionContext BlockExecutionContext::operator[](uint64_t const i) const
{
    // Remove constness to allow non-const mark()
    const_cast<SliceTracker &>(sliced_).mark(i);

    if (mode_ == ExecutionMode::Normal) {
        return {
            mode_,
            noop_call_tracer_,
            noop_state_tracer_,
            enable_native_transfer_tracing_};
    }

    if (mode_ == ExecutionMode::Tracing) {
        MONAD_ASSERT(
            !call_tracers_.empty() || !state_tracers_.empty(),
            "BlockExecutionContext: Tracing mode but both tracer arrays are empty (construction bug)");
        if (!call_tracers_.empty()) {
            // Call tracing mode
            return {
                mode_,
                *call_tracers_[i],
                noop_state_tracer_,
                enable_native_transfer_tracing_};
        } else {
            // State tracing mode
            return {
                mode_,
                noop_call_tracer_,
                *state_tracers_[i],
                enable_native_transfer_tracing_};
        }
    }

    if (mode_ == ExecutionMode::Simulation) {
        MONAD_ASSERT(!call_tracers_.empty(), "BlockExecutionContext: Simulation mode but call_tracers_ is empty (construction bug)");
        return {
            mode_,
            *call_tracers_[i],
            noop_state_tracer_,
            enable_native_transfer_tracing_};
    }
    MONAD_ASSERT(false, "BlockExecutionContext: invalid mode or construction");
}

MONAD_NAMESPACE_END
