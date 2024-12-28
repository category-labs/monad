#pragma once

/**
 * @file
 *
 * Definitions of fundamental execution event objects shared between readers
 * and the transaction execution engine (the writer). Most of these structures
 * are resident in shared memory segments mapped by both the writer and
 * the readers.
 */

#include <stddef.h>
#include <stdint.h>

#include <sys/queue.h>

#include <monad/event/event_types.h>

#ifdef __cplusplus
extern "C"
{
#endif

// clang-format off

/// Describes which event ring an event is recorded to; different categories
/// of events are recorded to different rings
enum monad_event_ring_type : uint8_t
{
    MONAD_EVENT_RING_EXEC,  ///< Core execution events
    MONAD_EVENT_RING_TRACE, ///< Performance tracing events
    MONAD_EVENT_RING_COUNT, ///< Number of recognized ring types
};

#define MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE (1UL << 24)

struct monad_event_header
{
    uint64_t seqno;              ///< Sequence number, for debugging only
    enum monad_event_type type;  ///< What kind of event this is
    uint16_t block_flow_id : 12; ///< ID representing block exec header
    uint16_t pop_scope  : 1;     ///< Ends the trace scope of an event
    uint16_t : 3;                ///< Unused bits
    uint32_t length : 24;        ///< Length of event payload
    uint32_t source_id : 8;      ///< ID representing origin thread
    uint32_t txn_num;            ///< Transaction number within block
    uint32_t : 32;               ///< Unused tail padding
    uint64_t epoch_nanos;        ///< Time event was recorded
};

// clang-format on

/// An IPC-style ring used to implement a lock-free MPMC ring for passing event
/// fragments between threads, potentially in different processes. This object
/// is not directly present in shared memory, but the control page and FIFO
/// buffer are.
struct monad_event_ring
{
    struct monad_event_ring_control *control;
    uint8_t *fifo_buf;
    size_t fifo_size;
};

struct monad_event_range
{
    uint64_t begin_byte;
    uint64_t end_byte;
};

/// Control register of the event ring, mapped in a shared memory page
struct monad_event_ring_control
{
    alignas(64) size_t next_byte;
    alignas(64) struct monad_event_range last_event_range;
};

/// Default location of the UNIX domain socket address for the event server
/// endpoint
#define MONAD_EVENT_DEFAULT_SOCKET_PATH "/tmp/monad_event.sock"

#ifdef __cplusplus
} // extern "C"
#endif
