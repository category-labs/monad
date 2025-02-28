#pragma once

/**
 * @file
 *
 * Definitions of fundamental event objects shared between readers and the
 * writer (the transaction execution daemon).
 */

#include <stddef.h>
#include <stdint.h>

#include <sys/types.h>

#ifdef __cplusplus
extern "C"
{
#endif

enum monad_event_type : uint16_t;
struct monad_event_block_exec_header;
struct monad_event_ring_header;

// clang-format off

/// Descriptor for an event; this fixed-size object describes the common
/// attributes of an event, and is broadcast to other threads via a shared
/// memory ring buffer (the threads are potentially in different processes).
/// The variably-sized extra content of the event (specific to each event type)
/// is called the "event payload"; it lives in a shared memory buffer called the
/// "payload buffer"; it can be accessed using this descriptor (see event.md)
struct monad_event_descriptor
{
    alignas(64) uint64_t seqno;  ///< Sequence number, for gap/liveness check
    enum monad_event_type type;  ///< What kind of event this is
    uint16_t block_flow_id;      ///< ID representing block exec header
    bool inline_payload;         ///< True -> payload stored inside descriptor
    uint8_t : 8;                 ///< Unused tail padding
    uint16_t : 16;               ///< Unused tail padding
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
    struct monad_event_ring_header *header;     ///< Event ring metadata
    struct monad_event_block_exec_header *blocks; ///< Optional block metadata
};

/// Control registers of the event ring; resource allocation within an event
/// ring, i.e., the reserving of an event descriptor slot and payload buffer
/// space to record an event, is tracked using this object
struct monad_event_ring_control
{
    alignas(64) uint64_t last_seqno; ///< Last seq. number allocated by writer
    uint64_t next_payload_byte;      ///< Next payload buffer byte to allocate
    alignas(64) uint64_t buffer_window_start; ///< See event.md documentation
};

/// Event ring shared memory files start with this header structure, which
/// describing the layout of the event ring
struct monad_event_ring_header
{
    char version[8];             ///< "RING_V01" versioning literal
    uint8_t metadata_hash[32];   ///< Checks that event_types.h matches
    size_t ring_capacity;        ///< # entries in event descriptor array
    size_t payload_buf_size;     ///< Byte size of payload buffer
    bool is_primary;             ///< True -> id tables follow payload buffer
    pid_t writer_pid;            ///< Process writing to the ring
    struct monad_event_ring_control control; ///< Tracks ring's state/status
};

// clang-format on

/// Map the shared memory for an event ring into our process' address space,
/// given a filesystem path to the event ring's shared memory file
int monad_event_ring_map(
    struct monad_event_ring *, char const *file_path, int *pidfd);

/// Remove an event ring's shared memory mappings from our process' address
/// space
void monad_event_ring_unmap(struct monad_event_ring *);

/// Return a description of the last error that occurred on this thread
char const *monad_event_get_last_error();

static uint8_t const MONAD_EVENT_RING_HEADER_VERSION[] = {
    'R', 'I', 'N', 'G', '_', 'V', '0', '1'};

#define MONAD_EVENT_DEFAULT_EXEC_EVENT_RING_PATH                               \
    "/dev/hugepages/monad-exec-events"

#ifdef __cplusplus
} // extern "C"
#endif
