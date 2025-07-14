#include <category/core/config.hpp>
#include <category/core/assert.h>
#include <monad/execution/fmt/event_trace_fmt.hpp> // NOLINT
#include <monad/execution/trace/event_trace.hpp>

#include <quill/Quill.h> // NOLINT
#include <quill/detail/LogMacros.h>

#include <chrono>
#include <cstdint>
#include <ostream>

MONAD_NAMESPACE_BEGIN

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
