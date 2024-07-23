#pragma once

#include <monad/config.hpp>

#include <quill/Quill.h>

#include <chrono>
#include <cstdint>
#include <ostream>
#include <utility>

#ifdef ENABLE_TRACING
    #include <monad/core/likely.h>
    #include <monad/fiber/priority_properties.hpp>

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

extern quill::Logger *tracer;

enum class TraceType : uint8_t
{
    StartBlock = 0,
    EndBlock = 1,
    StartTxn = 2,
    EndTxn = 3,
    StartSenderRecovery = 4,
    EndSenderRecovery = 5,
    StartExecution = 6,
    EndExecution = 7,
    StartStall = 8,
    EndStall = 9,
    StartRetry = 10,
    EndRetry = 11,
    StartReadAccount = 12,
    EndReadAccount = 13,
    StartReadStorage = 14,
    EndReadStorage = 15,
    StartReadCode = 16,
    EndReadCode = 17,
    StartCommit = 18,
    EndCommit = 19,
};

struct TraceEvent
{
    TraceType type;
    pid_t tid;
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
