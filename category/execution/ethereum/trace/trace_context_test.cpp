// Copyright (C) 2025-26 Category Labs, Inc.
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
#include <category/execution/ethereum/trace/trace_context.hpp>
#include <category/execution/ethereum/trace/trace_traits.hpp>

#include <gtest/gtest.h>

#include <cstddef>
#include <optional>
#include <span>
#include <stdexcept>
#include <vector>

using namespace monad;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

struct Ping
{
};

struct Count
{
    using returns = size_t;
};

struct CountingTracer
{
    using Signature = monad::Signature<Ping, Count>;

    size_t pings{0};
    size_t resets{0};

    void operator()(Ping const &)
    {
        ++pings;
    }

    size_t operator()(Count const &)
    {
        return pings;
    }

    void reset()
    {
        pings = 0;
        ++resets;
    }
};

struct ThrowingResetTracer
{
    using Signature = monad::Signature<>;

    void reset()
    {
        throw std::runtime_error{"reset failed"};
    }
};

struct NonResettableTracer
{
    using Signature = monad::Signature<Ping>;

    void operator()(Ping const &) {}
};

static_assert(Tracer<CountingTracer>);
static_assert(Resettable<CountingTracer>);
static_assert(!Resettable<NonResettableTracer>);

MONAD_ANONYMOUS_NAMESPACE_END

TEST(TxTraceContext, run_dispatches_to_first_suitable_tracer)
{
    CountingTracer first{};
    CountingTracer second{};
    std::vector<trace::TypeErasedTracer> const tracers{
        trace::TypeErasedTracer::erase(first),
        trace::TypeErasedTracer::erase(second)};
    TxTraceContext const trace_context{tracers};

    trace::emit<Ping>(trace_context);
    trace::emit<Ping>(trace_context);

    EXPECT_EQ(first.pings, 2u);
    EXPECT_EQ(second.pings, 0u);
    EXPECT_EQ(trace::emit<Count>(trace_context), std::optional<size_t>{2});
}

TEST(TxTraceContext, reset_is_broadcast_to_every_tracer)
{
    CountingTracer first{};
    CountingTracer second{};
    std::vector<trace::TypeErasedTracer> const tracers{
        trace::TypeErasedTracer::erase(first),
        trace::TypeErasedTracer::erase(second)};
    TxTraceContext const trace_context{tracers};

    trace::emit<Ping>(trace_context);
    second.pings = 3;

    trace_context.reset();

    EXPECT_EQ(first.resets, 1u);
    EXPECT_EQ(second.resets, 1u);
    EXPECT_EQ(first.pings, 0u);
    EXPECT_EQ(second.pings, 0u);
    EXPECT_EQ(trace::emit<Count>(trace_context), std::optional<size_t>{0});
}

TEST(TxTraceContext, reset_on_empty_context_is_noop)
{
    TxTraceContext const trace_context{};
    EXPECT_NO_THROW(trace_context.reset());
}

TEST(TxTraceContext, reset_propagates_tracer_exceptions)
{
    ThrowingResetTracer throwing{};
    trace::TypeErasedTracer const erased_tracer =
        trace::TypeErasedTracer::erase(throwing);
    std::span<trace::TypeErasedTracer const> const tracers{&erased_tracer, 1};
    TxTraceContext const trace_context{tracers};

    EXPECT_THROW(trace_context.reset(), std::runtime_error);
}

TEST(BlockTraceContext, slices_reset_independently)
{
    std::vector<CountingTracer> tx_tracers(2);
    BlockTraceContext const block_trace_context{
        tx_tracers.size(), std::span{tx_tracers}};

    trace::emit<Ping>(block_trace_context.slice(0));
    trace::emit<Ping>(block_trace_context.slice(1));

    block_trace_context.slice(0).reset();

    EXPECT_EQ(tx_tracers[0].resets, 1u);
    EXPECT_EQ(tx_tracers[0].pings, 0u);
    EXPECT_EQ(tx_tracers[1].resets, 0u);
    EXPECT_EQ(tx_tracers[1].pings, 1u);
}
