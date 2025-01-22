#pragma once

/**
 * @file
 *
 * Definitions of fundamental event objects shared between readers and the
 * writer (the transaction execution engine). Most of these structures are
 * resident in shared memory segments mapped by both the writer and the
 * readers.
 */

#include <stddef.h>
#include <stdint.h>

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

/// Size of a byte array needed to hold the largest possible event payload
#define MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE (1UL << 24)

/// Descriptor for a single event; this fixed-size object describes the common
/// attributes of an event, and is passed between threads via a shared memory
/// ring buffer (the threads are potentially in different processes). The
/// variably-sized extra content of the event (specific to each event type) is
/// called the "event payload", and lives in a shared memory segment called the
/// "payload buffer", which can be accessed using this descriptor
struct monad_event_descriptor
{
    alignas(64) uint64_t seqno;  ///< Sequence number, for gap/liveness check
    enum monad_event_type type;  ///< What kind of event this is
    uint16_t block_flow_id;      ///< ID representing block exec header
    uint8_t source_id;           ///< ID representing origin thread
    bool pop_scope;              ///< True -> ends the current trace scope
    bool inline_payload;         ///< True -> payload stored inside descriptor
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

/// Object that describes the event descriptor ring buffer, the event payload
/// byte buffer, and the ring buffer control structure. This object is not
/// directly present in shared memory, but all the pointer fields contain
/// addresses of shared memory objects
struct monad_event_ring
{
    struct monad_event_descriptor
        *descriptors;                  ///< Event descriptor ring array
    size_t capacity;                   ///< Size of `descriptors` array
    uint8_t *payload_buf;              ///< Payload buffer start address
    size_t payload_buf_size;           ///< Payload buffer size in bytes
    struct monad_event_ring_control
        *control;                      ///< Keeps track of ring state/status
};

// clang-format on

/// Control registers of the event ring, mapped in a shared memory page;
/// resource allocation within an event ring, i.e., the reserving of an event
/// descriptor slot and payload buffer space to record an event, is tracked
/// using this object
struct monad_event_ring_control
{
    alignas(64) uint64_t last_seqno; ///< Last sequence number allocated
    uint64_t next_payload_byte; ///< Next payload buffer byte to allocate
    alignas(64) uint64_t buffer_window_start; ///< See event.md documentation
};

/// Default location of the UNIX domain socket address for the event server
/// endpoint
#define MONAD_EVENT_DEFAULT_SOCKET_PATH "/tmp/monad_event.sock"

#ifdef __cplusplus
} // extern "C"
#endif
