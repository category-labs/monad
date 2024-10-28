#pragma once

/**
 * @file
 *
 * Event recorder interface. There are four things in this file:
 *
 *   1. The macros used for recording events. These are needed by any file
 *      that wishes to record events, along with event.h
 *
 *   2. The initialization function to configure the recorder, i.e., setting
 *      the amount of memory for the recorder ring and payload page pool
 *
 *   3. Minimum, maximum, and default values for various memory configuration
 *      options
 *
 *   4. The function to set the global domain enablement mask. This enables
 *      or disables recording globally per domain. It must be called at
 *      least once during initialization (the default mask is 0 -- nothing
 *      enabled) but can be used to quickly enable/disable verbose domains
 *      (such as the performance tracing domains) when they are not needed
 */

#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

enum monad_event_type : uint16_t;

enum monad_event_flags : uint8_t
{
    MONAD_EVENT_POP_SCOPE = 0b1
};

/// Record an event with the given type, whose event payload is described by
/// the given (PTR, SIZE) pair that will be memcpy'ed to a payload page
#define MONAD_EVENT_MEMCPY(EVENT_TYPE, FLAGS, PTR, SIZE)                       \
    monad_event_record((EVENT_TYPE), (FLAGS), (PTR), (SIZE))

/// Record an event with the given type, whose event payload is described by
/// the given l-value expression
#define MONAD_EVENT_EXPR(EVENT_TYPE, FLAGS, LEXPR)                             \
    MONAD_EVENT_MEMCPY((EVENT_TYPE), (FLAGS), &(LEXPR), sizeof(LEXPR))

/// Record an event without an event payload
#define MONAD_EVENT(EVENT_TYPE, FLAGS)                                         \
    MONAD_EVENT_MEMCPY((EVENT_TYPE), (FLAGS), nullptr, 0)

#if MONAD_ENABLE_TRACE

#define MONAD_TRACE_MEMCPY(...) MONAD_EVENT_MEMCPY(__VA_ARGS__)
#define MONAD_TRACE_EXPR(...) MONAD_EVENT_EXPR(__VA_ARGS__)
#define MONAD_TRACE(...) MONAD_EVENT(__VA_ARGS__)

#else

#define MONAD_TRACE_MEMCPY(...) MONAD_EVENT_MEMCPY(__VA_ARGS__)
#define MONAD_TRACE_EXPR(...) MONAD_EVENT_EXPR(__VA_ARGS__)
#define MONAD_TRACE(...) MONAD_EVENT(__VA_ARGS__)

#endif

/// Initialize the event recorder's memory allocation parameters; this must be
/// called prior to calling `monad_event_recorder_set_domain_mask` for the
/// first time, otherwise it will have no effect and will return EBUSY
int monad_event_recorder_configure(
    uint8_t ring_shift, size_t payload_page_size, uint16_t payload_page_count);

/// Set which domains are enabled in the recorder
static uint64_t monad_event_recorder_set_domain_mask(uint64_t domain_mask);

/// Stops the recorder system and returns once the sync thread has drained
/// all pending events from the recorder queue
void monad_event_recorder_halt();

/// Return a description of the last recorder error that occurred on this thread
char const *monad_event_recorder_get_last_error();

/// Take a timestamp, in nanoseconds since the UNIX epoch
static uint64_t monad_event_get_epoch_nanos();

/// Take a timestamp, using a clock known to the recording infrastructure;
/// it will be translated to epoch nanos before being seen by consumers
static uint64_t monad_event_timestamp();

/// Record an event; usually invoked via the `MONAD_EVENT_` family of macros
static void monad_event_record(
    enum monad_event_type event_type, uint8_t flags, void const *payload,
    size_t payload_size);

/// __attribute__((constructor)) priority of the event recorder's constructor
#define MONAD_EVENT_RECORDER_CTOR_PRIO 1000

/*
 * Min, max, and default memory sizes
 */

#define MONAD_EVENT_RECORDER_DEFAULT_RING_SHIFT (20)
#define MONAD_EVENT_RECORDER_MIN_RING_SHIFT (12)
#define MONAD_EVENT_RECORDER_MAX_RING_SHIFT (40)

#define MONAD_EVENT_DEFAULT_PAYLOAD_PAGE_SIZE (1UL << 24)
#define MONAD_EVENT_MIN_PAYLOAD_PAGE_SIZE (1UL << 20)
#define MONAD_EVENT_MAX_PAYLOAD_PAGE_SIZE (1UL << 32)

#define MONAD_EVENT_DEFAULT_PAYLOAD_PAGE_COUNT (32)
#define MONAD_EVENT_MIN_PAYLOAD_PAGE_COUNT (20)

#define MONAD_EVENT_RECORDER_INTERNAL
#include "event_recorder_inline.h"
#undef MONAD_EVENT_RECORDER_INTERNAL

#ifdef __cplusplus
} // extern "C"
#endif
