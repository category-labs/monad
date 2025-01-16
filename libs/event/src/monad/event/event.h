#pragma once

/**
 * @file
 *
 * Definitions of fundamental event objects shared between readers and the
 * writer (the transaction execution daemon).
 */

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

enum monad_event_type : uint16_t;

// clang-format off

/// Size of a byte array needed to hold the largest possible event payload
#define MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE (1UL << 24)

/// Descriptor for a single event; this fixed-size object describes the common
/// attributes of an event, and is passed between threads via a shared memory
/// ring buffer (the threads are potentially in different processes). The
/// variably-sized extra content of the event (specific to each event type) is
/// called the "event payload", and lives in a shared memory buffer called the
/// "payload buffer", which can be accessed using this descriptor (see event.md)
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
    uint32_t txn_id;             ///< 0 == no txn, else ID == txn num + 1
    uint64_t epoch_nanos;        ///< Time event was recorded
    union
    {
        uint64_t payload_buf_offset; ///< Payload buffer byte offset
        uint8_t payload[32];         ///< Payload contents if inline_payload
    };
};

static_assert(sizeof(struct monad_event_descriptor) == 64);

/// Describes a shared memory event ring that has been mapped into the address
/// space of the current process
struct monad_event_ring
{
    struct monad_event_descriptor *descriptors; ///< Event descriptor ring array
    uint8_t *payload_buf;                       ///< Payload buffer base address
    struct monad_event_ring_control *control;   ///< Tracks ring's state/status
    size_t capacity;                            ///< Size of descriptors array
    size_t payload_buf_size;                    ///< Bytes in payload_buf
    void *ring_db_map_base;                     ///< API convenience (see impl)
};

/// Describes the state that an event ring is in (each ring may be enabled or
/// disabled independently)
enum monad_event_ring_state : uint8_t
{
    MONAD_EVENT_RING_OFFLINE = 0,    ///< Cannot mmap ring (no memory allocated)
    MONAD_EVENT_RING_CONFIGURED = 1, ///< Can mmap ring, but recording disabled
    MONAD_EVENT_RING_ENABLED = 2     ///< Event ring actively recording
};

/// Control registers of the event ring; resource allocation within an event
/// ring, i.e., the reserving of an event descriptor slot and payload buffer
/// space to record an event, is tracked using this shared-memory-resident
/// object
struct monad_event_ring_control
{
    alignas(64) enum monad_event_ring_state
        ring_state;                  ///< Readiness state this event ring is in
    alignas(64) uint64_t last_seqno; ///< Last seq. number allocated by writer
    uint64_t next_payload_byte;      ///< Next payload buffer byte to allocate
    alignas(64) uint64_t buffer_window_start; ///< See event.md documentation
};

// clang-format on

/// Remove an event ring's shared memory mappings from our process' address
/// space
void monad_event_ring_unmap(struct monad_event_ring *);

#ifdef __cplusplus
} // extern "C"
#endif
