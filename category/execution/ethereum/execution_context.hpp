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

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

enum class ExecutionMode : uint8_t
{
    Normal,
    Simulation,
    Tracing
};

/// Per-transaction execution context.
///
/// In Normal mode, the tracer references point to shared no-op singletons
/// (safe because they have no mutable state). In Simulation/Tracing mode,
/// each TxExecutionContext holds references to per-transaction tracer
/// instances that are not aliased by any other fiber.
struct TxExecutionContext
{
    ExecutionMode mode;
    CallTracerBase &call_tracer;
    trace::StateTracer &state_tracer;
    bool const trace_transfers;
};

/// Tracks that each transaction index is sliced at most once.
///
/// Uses a std::vector<bool> as a dynamic bitset. One allocation of N bits
/// covers arbitrary transaction counts.
class SliceTracker
{
    std::vector<bool> bits_;
    size_t num_bits_;

public:
    explicit SliceTracker(size_t n)
        : bits_(n, false)
        , num_bits_(n)
    {
    }

    /// Marks bit i as sliced. Aborts if already set.
    void mark(size_t i)
    {
        MONAD_ASSERT(i < num_bits_);
        MONAD_ASSERT_PRINTF(
            !bits_[i], "BlockExecutionContext: index %zu sliced twice", i);
        bits_[i] = true;
    }
};

/// Block-level execution context that bundles the execution mode and
/// per-transaction tracer storage.
///
/// Constructed once before fibers launch. Immutable after construction
/// (safe to share across fibers). Provides operator[] to slice out a
/// per-transaction TxExecutionContext for each fiber.
///
/// In Normal mode: zero per-tx allocations. All fibers share a pair of
/// no-op tracer singletons owned by this object. This is data-race free
/// because NoopCallTracer has no data members and StateTracer(monostate)
/// is never mutated.
///
/// In Tracing mode: the caller owns a per-tx call tracer array and passes
/// it as a span. State tracers are no-ops (shared singletons).
///
/// In Simulation mode: the caller owns per-tx tracer arrays for both
/// call and state tracers. operator[] indexes into these arrays, and a
/// SliceTracker ensures each index is used at most once.
class BlockExecutionContext
{
public:
    /// Normal mode: zero per-tx allocations. Shared no-op tracers.
    static BlockExecutionContext normal(size_t size);

    /// Call tracing mode: caller provides per-tx call tracers. State tracers
    /// are no-ops.
    static BlockExecutionContext call_tracing(
        size_t size, std::span<std::unique_ptr<CallTracerBase>> call_tracers);

    /// State tracing mode: caller provides per-tx state tracers. Call tracers
    /// are no-ops.
    static BlockExecutionContext state_tracing(
        size_t size,
        std::span<std::unique_ptr<trace::StateTracer>> state_tracers);

    /// Simulation mode: caller provides per-tx call and state tracer arrays.
    static BlockExecutionContext simulation(
        size_t size, std::span<std::unique_ptr<CallTracerBase>> call_tracers,
        std::span<std::unique_ptr<trace::StateTracer>> state_tracers,
        bool enable_native_transfer_tracing = false);

    ExecutionMode mode() const
    {
        return mode_;
    }

    /// Returns a per-transaction context for fiber i.
    ///
    /// In Normal mode: returns references to shared no-op singletons.
    /// In Call tracing mode: returns per-tx call tracer, shared no-op state
    /// tracer. In State tracing mode: returns shared no-op call tracer, per-tx
    /// state tracer. In Simulation mode: returns per-tx call and state tracers.
    ///   Precondition (checked at runtime): each i is sliced at most once.
    TxExecutionContext operator[](uint64_t i) const;

private:
    BlockExecutionContext(
        ExecutionMode mode, size_t size,
        std::span<std::unique_ptr<CallTracerBase>> call_tracers,
        std::span<std::unique_ptr<trace::StateTracer>> state_tracers,
        bool enable_native_transfer_tracing = false);

    ExecutionMode mode_;
    std::span<std::unique_ptr<CallTracerBase>> call_tracers_;
    std::span<std::unique_ptr<trace::StateTracer>> state_tracers_;
    bool enable_native_transfer_tracing_ = false;

    mutable NoopCallTracer noop_call_tracer_;
    mutable trace::StateTracer noop_state_tracer_{std::monostate{}};

    mutable SliceTracker sliced_;
};

MONAD_NAMESPACE_END
