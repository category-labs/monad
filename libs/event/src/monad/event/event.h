#pragma once

/**
 * @file
 *
 * Definitions of fundamental execution event objects shared between readers
 * and the transaction execution engine (the writer). Most of these structures
 * are resident in shared memory segments mapped by both the writer and
 * the readers.
 */

#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>

#include <sys/queue.h>

#include <monad/event/event_types.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_event_payload_page_pool;

// clang-format off

/// Describes which event ring an event is recorded to; different categories
/// of events are recorded to different rings
enum monad_event_ring_type : uint8_t
{
    MONAD_EVENT_RING_EXEC,  ///< Core execution events
    MONAD_EVENT_RING_TRACE, ///< Performance tracing events
    MONAD_EVENT_RING_COUNT, ///< Number of recognized ring types
};

#define MONAD_EVENT_MAX_INLINE 224

struct monad_event_header
{
    _Atomic(uint64_t) seqno;     ///< Sequence number, for gap/liveness check
    enum monad_event_type type;  ///< What kind of event this is
    uint16_t inline_length;      ///< Used bytes in payload buffer for fragment
    uint16_t frag_no;            ///< Fragment number (for reassembly)
    uint16_t frag_count;         ///< Total number of fragments
    uint32_t pop_scope : 1;      ///< Ends the trace scope of an event
    uint32_t total_length : 23;  ///< Total size of event payload, all fragments
    uint32_t source_id : 8;      ///< ID representing origin thread
    uint32_t block_flow_id : 12; ///< ID representing block exec header
    uint32_t txn_num : 20;       ///< Transaction number within block
    uint64_t epoch_nanos;        ///< Time event was recorded
};

struct monad_event_fragment
{
    struct monad_event_header header; ///< Header for this fragment
    uint8_t payload[MONAD_EVENT_MAX_INLINE]; ///< Fragment payload
};

static_assert(sizeof(struct monad_event_fragment) == 256);

// clang-format on

/// An IPC-style ring used to implement a lock-free MPMC ring for passing event
/// fragments between threads, potentially in different processes. This object
/// is not directly present in shared memory, but the control page and fragment
/// table are.
struct monad_event_ring
{
    struct monad_event_ring_control *control;
    struct monad_event_fragment *fragment_table;
    size_t capacity_mask;
    size_t capacity;
};

/// Control register of the event ring, mapped in a shared memory page
struct monad_event_ring_control
{
    alignas(64) __uint128_t seqno_fragment_next;
};

/// Default location of the UNIX domain socket address for the event server
/// endpoint
#define MONAD_EVENT_DEFAULT_SOCKET_PATH "/tmp/monad_event.sock"

#ifdef __cplusplus
} // extern "C"
#endif
