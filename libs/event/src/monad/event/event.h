#pragma once

/**
 * @file
 *
 * Definitions of fundamental execution event objects shared between readers
 * and the transaction execution engine (the writer). Most of these are
 * resident in shared memory segments.
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

/// Describes which event queue an event is recorded to; different categories
/// of events are recorded to different queues
enum monad_event_queue_type : uint8_t
{
    MONAD_EVENT_QUEUE_EXEC,  ///< Core execution events
    MONAD_EVENT_QUEUE_TRACE, ///< Performance tracing events
    MONAD_EVENT_QUEUE_COUNT, ///< Number of recognized queue types
};

/// Descriptor for a single event; this fixed-size object is passed via a
/// shared memory queue between threads, potentially in different processes;
/// the rest of the (variably-sized) event is called the "event payload", and
/// lives in a shared memory heap that can be accessed using this descriptor
struct monad_event_descriptor
{
    _Atomic(uint64_t) seqno;     ///< Sequence number, for gap/liveness check
    enum monad_event_type type;  ///< What kind of event this is
    uint16_t payload_page;       ///< Shared memory page containing payload
    uint32_t offset;             ///< Offset in page where payload starts
    uint32_t pop_scope : 1;      ///< Ends the trace scope of an event
    uint32_t length : 23;        ///< Size of event payload
    uint32_t source_id : 8;      ///< ID representing origin thread
    uint32_t block_flow_id : 12; ///< ID representing block exec header
    uint32_t txn_num : 20;       ///< Transaction number within block
    uint64_t epoch_nanos;        ///< Time event was recorded
};

// clang-format on

/// An IPC-style ring used to implement a lock-free MPMC queue for passing
/// event descriptors between threads, potentially in different processes.
/// This object is not directly present in shared memory, but the control page
/// and descriptor table are.
struct monad_event_ring
{
    struct monad_event_ring_control *control;
    struct monad_event_descriptor *descriptor_table;
    size_t capacity_mask;
    size_t capacity;
    int control_fd;
    int descriptor_table_fd;
};

/// Control register of the event ring, mapped in a shared memory page
struct monad_event_ring_control
{
    alignas(64) _Atomic(uint64_t) prod_next;
};

/// This structure appears at the start of the shared memory region for an
/// event payload page
struct monad_event_payload_page
{
    // Cache line read by readers, modified by writers
    alignas(64) _Atomic(uint64_t) overwrite_seqno;
    // Cache line *only* used by writer (except for the exportshm utility). The
    // pointers here point into the writer's address space
    alignas(64) uint8_t *page_base;
    uint8_t *heap_begin;
    uint8_t *heap_next;
    uint8_t *heap_end;
    uint64_t event_count;
    uint64_t alloc_count;
    TAILQ_ENTRY(monad_event_payload_page) page_link;
    /* Cache line holding lifetime-constant values */
    alignas(64) struct monad_event_payload_page_pool *page_pool;
    int memfd;
    uint16_t page_id;
    char page_name[26];
};

/// Maximum number of events that can be copied out in a single call to
/// monad_event_reader_bulk_copy
#define MONAD_EVENT_MAX_BULK_COPY                                              \
    ((1UL << 21) / sizeof(struct monad_event_descriptor))

/// Default location of the UNIX domain socket address for the event server
/// endpoint
#define MONAD_EVENT_DEFAULT_SOCKET_PATH "/tmp/monad_event.sock"

#ifdef __cplusplus
} // extern "C"
#endif
