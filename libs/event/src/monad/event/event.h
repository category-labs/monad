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

/// Descriptor for a single event; this fixed-size object is passed between
/// threads via a shared memory ring buffer (the threads are potentially in
/// different processes). The extra content of the (variably-sized) event is
/// called the "event payload", and lives in a shared memory heap that can be
/// accessed using this descriptor
struct monad_event_descriptor
{
    _Atomic(uint64_t) seqno;     ///< Sequence number, for gap/liveness check
    enum monad_event_type type;  ///< What kind of event this is
    uint16_t block_flow_id;      ///< ID representing block exec header
    uint8_t source_id;           ///< ID representing origin thread
    bool pop_scope;              ///< Ends the trace scope of an event
    bool inline_payload;         ///< True -> payload is stored inline
    uint8_t : 8;                 ///< Unused tail padding
    uint32_t length;             ///< Size of event payload
    uint32_t txn_num;            ///< Transaction number within block
    uint64_t epoch_nanos;        ///< Time event was recorded
    union
    {
        uint64_t payload_buf_offset; ///< Payload buffer byte offset
        uint8_t payload[32];         ///< Payload contents if inline_payload
    };
};

static_assert(sizeof(struct monad_event_descriptor) == 64);

// clang-format on

/// An IPC-style ring used to implement a lock-free MPMC ring for passing event
/// descriptors between threads, potentially in different processes. This
/// object is not directly present in shared memory, but the control page,
/// descriptor table, and payload buffer are.
struct monad_event_ring
{
    struct monad_event_ring_control *control;
    struct monad_event_descriptor *descriptor_table;
    size_t capacity;
    uint8_t *payload_buf;
    size_t payload_buf_size;
};

struct monad_event_ring_writer_state
{
    alignas(16) uint64_t last_seqno;
    uint64_t next_payload_byte;
};

/// Control registers of the event ring, mapped in a shared memory page
struct monad_event_ring_control
{
    alignas(64) struct monad_event_ring_writer_state wr_state;
    alignas(64) uint64_t buffer_window_start;
};

#ifdef __cplusplus
} // extern "C"
#endif
