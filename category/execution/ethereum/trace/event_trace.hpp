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

#include <category/core/config.hpp>

#include <quill/Quill.h>

#include <chrono>
#include <cstdint>
#include <ostream>
#include <utility>

#ifdef ENABLE_EVENT_TRACING
    #include <category/core/likely.h>
    #include <category/core/fiber/priority_properties.hpp>

    #include <boost/fiber/operations.hpp>

    #define TRACE_BLOCK_EVENT(enum)                                            \
        auto const timer_##enum =                                              \
            TraceTimer{TraceEvent{TraceType::enum, block.header.number}};

    #define TRACE_TXN_EVENT(enum)                                              \
        auto const timer_##enum = TraceTimer{TraceEvent{                       \
            TraceType::enum, [] {                                              \
                auto const *const props =                                      \
                    boost::fibers::context::active()->get_properties();        \
                                                                               \
                if (MONAD_LIKELY(props)) {                                     \
                    return dynamic_cast<                                       \
                               monad::fiber::PriorityProperties const &>(      \
                               *props)                                         \
                        .get_priority();                                       \
                }                                                              \
                else {                                                         \
                    return 0ul;                                                \
                }                                                              \
            }()}};
#else
    #define TRACE_BLOCK_EVENT(enum)
    #define TRACE_TXN_EVENT(enum)
#endif

MONAD_NAMESPACE_BEGIN

extern quill::Logger *event_tracer;

enum class TraceType : uint8_t
{
    StartBlock = 0,
    StartTxn = 1,
    StartSenderRecovery = 2,
    StartExecution = 3,
    StartStall = 4,
    StartRetry = 5,
    EndBlock = 6,
    EndTxn = 7,
    EndSenderRecovery = 8,
    EndExecution = 9,
    EndStall = 10,
    EndRetry = 11,
};

struct TraceEvent
{
    TraceType type;
    std::chrono::nanoseconds time;
    uint64_t value;

    TraceEvent(TraceType, uint64_t value);
    friend std::ostream &operator<<(std::ostream &, TraceEvent const &);
};

static_assert(sizeof(TraceEvent) == 24);
static_assert(alignof(TraceEvent) == 8);

struct TraceTimer
{
    TraceEvent orig;

    explicit TraceTimer(TraceEvent const &);
    ~TraceTimer();
};

static_assert(sizeof(TraceTimer) == 24);
static_assert(alignof(TraceTimer) == 8);

MONAD_NAMESPACE_END
