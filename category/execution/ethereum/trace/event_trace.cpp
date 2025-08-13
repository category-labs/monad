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

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/execution/ethereum/fmt/event_trace_fmt.hpp> // NOLINT
#include <category/execution/ethereum/trace/event_trace.hpp>

#include <quill/Quill.h> // NOLINT
#include <quill/detail/LogMacros.h>

#include <chrono>
#include <cstdint>
#include <ostream>

MONAD_NAMESPACE_BEGIN

quill::Logger *event_tracer = nullptr;

TraceTimer::TraceTimer(TraceEvent const &event)
    : orig{event}
{
    QUILL_LOG_INFO(event_tracer, "{}", event);
}

TraceTimer::~TraceTimer()
{
    QUILL_LOG_INFO(
        event_tracer,
        "{}",
        TraceEvent{
            [&] {
                switch (orig.type) {
                case TraceType::StartBlock:
                    return TraceType::EndBlock;
                case TraceType::StartTxn:
                    return TraceType::EndTxn;
                case TraceType::StartSenderRecovery:
                    return TraceType::EndSenderRecovery;
                case TraceType::StartExecution:
                    return TraceType::EndExecution;
                case TraceType::StartStall:
                    return TraceType::EndStall;
                case TraceType::StartRetry:
                    return TraceType::EndRetry;
                default:
                    MONAD_ASSERT(false);
                }
            }(),
            orig.value});
}

TraceEvent::TraceEvent(TraceType const type, uint64_t const value)
    : type{type}
    , time{std::chrono::steady_clock::now().time_since_epoch()}
    , value{value}
{
}

std::ostream &operator<<(std::ostream &os, TraceEvent const &event)
{
    os.write(reinterpret_cast<char const *>(&event), sizeof(TraceEvent));
    return os;
}

MONAD_NAMESPACE_END
