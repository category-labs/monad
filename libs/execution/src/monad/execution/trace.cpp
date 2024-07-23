#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/execution/fmt/trace_fmt.hpp> // NOLINT
#include <monad/execution/trace.hpp>

#include <quill/Quill.h> // NOLINT
#include <quill/detail/LogMacros.h>

#include <chrono>
#include <cstdint>
#include <ostream>
#include <unistd.h>

MONAD_NAMESPACE_BEGIN

TraceTimer::TraceTimer(TraceEvent const &event)
    : orig{event}
{
    QUILL_LOG_INFO(tracer, "{}", event);
}

TraceTimer::~TraceTimer()
{
    auto const type = [&] {
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
        case TraceType::StartReadAccount:
            return TraceType::EndReadAccount;
        case TraceType::StartReadStorage:
            return TraceType::EndReadStorage;
        case TraceType::StartReadCode:
            return TraceType::EndReadCode;
        case TraceType::StartCommit:
            return TraceType::EndCommit;
        default:
            MONAD_ASSERT(false);
        }
    }();
    QUILL_LOG_INFO(tracer, "{}", TraceEvent{type, orig.value});
}

TraceEvent::TraceEvent(TraceType const type, uint64_t const value)
    : type{type}
    , tid(gettid())
    , time{std::chrono::steady_clock::now().time_since_epoch()}
    , value{value}
{
}

std::ostream &operator<<(std::ostream &os, TraceEvent const &event)
{
    os.write(reinterpret_cast<char const *>(&event.type), sizeof(event.type));
    os.write(reinterpret_cast<char const *>(&event.tid), sizeof(event.tid));
    os.write(reinterpret_cast<char const *>(&event.time), sizeof(event.time));
    os.write(reinterpret_cast<char const *>(&event.value), sizeof(event.value));
    return os;
}

MONAD_NAMESPACE_END
