#pragma once

/**
 * @file
 *
 * Core definitions of event enumeration types and structures
 */

#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

// clang-format off

/// Events are organized into numerical ranges called "domains"; an event
/// domain behaves like a category of events, and event capture can be
/// enabled/disabled at the domain level. The domain is the most significant
/// 8 bits of an event's enumeration code
enum monad_event_domain : uint8_t
{
    MONAD_EVENT_DOMAIN_NONE,        ///< So that zero initialization == invalid
    MONAD_EVENT_DOMAIN_INTERNAL,    ///< Events occurring inside event recorder
    MONAD_EVENT_DOMAIN_PERF,        ///< Events needed for performance tracer
    MONAD_EVENT_DOMAIN_BLOCK,       ///< Block-related events
    MONAD_EVENT_DOMAIN_TXN,         ///< Transaction-related events
    MONAD_EVENT_DOMAIN_FIBER,       ///< Events related to the fiber subsystem
    MONAD_EVENT_DOMAIN_STATS,       ///< Low-volume summary statistics
    MONAD_EVENT_DOMAIN_READ_STATE,  ///< State querying (for pre-state tracer)
    MONAD_EVENT_DOMAIN_WRITE_STATE, ///< State mutating
    MONAD_EVENT_DOMAIN_OPCODE,      ///< For opcode-level tracing
    MONAD_EVENT_DOMAIN_COUNT        ///< Number of domains
};

// We currently use uint64_t bitmasks to enable/disable domains so only 64
// domains are supported for now
static_assert(MONAD_EVENT_DOMAIN_COUNT < 64);

/// Each type of event is assigned a unique value in this enumeration; all
/// metadata about events is defined in ".def" files, which are processed in
/// various ways using the C preprocessor; there is one ".def" file for
/// each event domain
enum monad_event_type : uint16_t
{
    MONAD_EVENT_NONE = 0,

    // The strategy followed here is that the first event definition
    // (which uses the MONAD_EVENT_DEF_FIRST macro) is assigned a numeric
    // value of (<domain> << 8) and all subsequent enumerations have no
    // explicit value, so they are assigned sequentially, e.g., for the
    // internal and block domains, this will be preprocessed into:
    //
    //    /* internal.def */
    //    MONAD_EVENT_THREAD_CREATE = (uint16_t)MONAD_EVENT_DOMAIN_INTERNAL << 8,
    //    MONAD_EVENT_THREAD_EXIT,    // No explicit value, +1 from previous
    //    MONAD_EVENT_SYNC_THR_INIT,  // As above
    //    ... more internal event types
    //
    //    /* block.def */
    //    MONAD_EVENT_BLOCK_START = (uint16_t)MONAD_EVENT_DOMAIN_BLOCK << 8,
    //    MONAD_EVENT_BLOCK_END,      // Sequentially assigned, as above
    //    ... more block event types

#define MONAD_EVENT_DEF_FIRST(C_SUFFIX, CAMEL_NAME, TRACE_FLAGS, DESC) \
    MONAD_EVENT_ ## C_SUFFIX = (uint16_t)MONAD_EVENT_DOMAIN_INTERNAL << 8,
#define MONAD_EVENT_DEF(C_SUFFIX, CAMEL_NAME, TRACE_FLAGS, DESC) \
    MONAD_EVENT_ ## C_SUFFIX,
    #include "definitions/internal.def"

#define MONAD_EVENT_DEF_FIRST(C_SUFFIX, CAMEL_NAME, TRACE_FLAGS, DESC) \
    MONAD_EVENT_ ## C_SUFFIX = (uint16_t)MONAD_EVENT_DOMAIN_PERF << 8,
#define MONAD_EVENT_DEF(C_SUFFIX, CAMEL_NAME, TRACE_FLAGS, DESC) \
    MONAD_EVENT_ ## C_SUFFIX,
    #include "definitions/perf.def"

#define MONAD_EVENT_DEF_FIRST(C_SUFFIX, CAMEL_NAME, TRACE_FLAGS, DESC) \
    MONAD_EVENT_ ## C_SUFFIX = (uint16_t)MONAD_EVENT_DOMAIN_BLOCK << 8,
#define MONAD_EVENT_DEF(C_SUFFIX, CAMEL_NAME, TRACE_FLAGS, DESC) \
    MONAD_EVENT_ ## C_SUFFIX,
    #include "definitions/block.def"

#define MONAD_EVENT_DEF_FIRST(C_SUFFIX, CAMEL_NAME, TRACE_FLAGS, DESC) \
    MONAD_EVENT_ ## C_SUFFIX = (uint16_t)MONAD_EVENT_DOMAIN_TXN << 8,
#define MONAD_EVENT_DEF(C_SUFFIX, CAMEL_NAME, TRACE_FLAGS, DESC) \
    MONAD_EVENT_ ## C_SUFFIX,
    #include "definitions/txn.def"

#define MONAD_EVENT_DEF_FIRST(C_SUFFIX, CAMEL_NAME, TRACE_FLAGS, DESC) \
    MONAD_EVENT_ ## C_SUFFIX = (uint16_t)MONAD_EVENT_DOMAIN_FIBER << 8,
#define MONAD_EVENT_DEF(C_SUFFIX, CAMEL_NAME, TRACE_FLAGS, DESC) \
    MONAD_EVENT_ ## C_SUFFIX,
    #include "definitions/fiber.def"

#define MONAD_EVENT_DEF_FIRST(C_SUFFIX, CAMEL_NAME, TRACE_FLAGS, DESC) \
    MONAD_EVENT_ ## C_SUFFIX = (uint16_t)MONAD_EVENT_DOMAIN_STATS << 8,
#define MONAD_EVENT_DEF(C_SUFFIX, CAMEL_NAME, TRACE_FLAGS, DESC) \
    MONAD_EVENT_ ## C_SUFFIX,
    #include "definitions/stats.def"
};

/// Extract the domain from the event code
#define MONAD_EVENT_DOMAIN(X) ((enum monad_event_domain)((X) >> 8))

/// Extract the "domain relative code", i.e., the low 8 bits of the event
#define MONAD_EVENT_DRCODE(X) ((uint8_t)((X) & 0xFF))

/// Convert a monad_event_domain value to a bitmask
#define MONAD_EVENT_DOMAIN_MASK(X) ((uint64_t)1UL << ((uint8_t)(X) - 1))

/// Descriptor for a single event; this fixed-size object is passed via a
/// shared memory queue between threads, potentially in different processes;
/// the rest of the (variably-sized) event is called the "event payload", and
/// lives in a shared memory heap that can be accessed using this descriptor
struct monad_event_descriptor
{
    enum monad_event_type type;  ///< What kind of event this is
    uint16_t payload_page;       ///< Shared memory page containing payload
    uint32_t offset;             ///< Offset in page where payload starts
    uint32_t pop_scope : 1;      ///< Ends the trace scope of an event
    uint32_t length : 23;        ///< Size of event payload
    uint32_t source_id : 8;      ///< ID describing origin thread
    uint32_t page_generation;    ///< Page generation number
    uint64_t seqno;              ///< Sequence number, for gap detection
    uint64_t epoch_nanos;        ///< Time event was recorded
};

/// Default location of the UNIX domain socket address for the event server
/// endpoint
#define MONAD_EVENT_DEFAULT_SOCKET_PATH "/tmp/monad_event.sock"

#define MONAD_EVENT_DOMAIN_ENABLE_ALL (~(uint64_t)0)
#define MONAD_EVENT_DOMAIN_ENABLE_NONE (0)

// clang-format on

#ifdef __cplusplus
} // extern "C"
#endif
