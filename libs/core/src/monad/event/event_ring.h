#pragma once

/**
 * @file
 *
 * Definition of the event ring structures and the functions which create and
 * mmap event rings.
 */

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_event_descriptor;
struct monad_event_iterator;
struct monad_event_recorder;
struct monad_event_ring_header;

// clang-format off

/// Describes a shared memory event ring that has been mapped into the address
/// space of the current process
struct monad_event_ring
{
    int mmap_prot;                              ///< Our pages mmap'ed with this
    struct monad_event_ring_header *header;     ///< Event ring metadata
    struct monad_event_descriptor *descriptors; ///< Event descriptor ring array
    uint8_t *payload_buf;                       ///< Payload buffer base address
};

/// Descriptor for an event; this fixed-size object describes the common
/// attributes of an event, and is broadcast to other threads via a shared
/// memory ring buffer (the threads are potentially in different processes).
/// The variably-sized extra content of the event (specific to each event type)
/// is called the "event payload"; it lives in a shared memory buffer called the
/// "payload buffer"; it can be accessed using this descriptor (see event.md)
struct monad_event_descriptor
{
    alignas(64) uint64_t seqno;  ///< Sequence number, for gap/liveness check
    uint16_t event_type;         ///< What kind of event this is
    bool inline_payload;         ///< True -> payload stored inside descriptor
    uint8_t : 8;                 ///< Unused tail padding
    uint32_t payload_size;       ///< Size of event payload
    uint64_t epoch_nanos;        ///< Time event was recorded
    uint64_t : 64 ;              ///< Reserved (will be used in PR2)
    union
    {
        uint64_t payload_buf_offset; ///< Unwrapped offset of payload in p. buf
        uint8_t payload[32];         ///< Payload contents if inline_payload
    };
};

static_assert(sizeof(struct monad_event_descriptor) == 64);

/// Describes the size of an event ring's primary data structures
struct monad_event_ring_size
{
    size_t descriptor_capacity; ///< # entries in event descriptor array
    size_t payload_buf_size;    ///< Byte size of payload buffer
};

/// Control registers of the event ring; resource allocation within an event
/// ring, i.e., the reserving of an event descriptor slot and payload buffer
/// space to record an event, is tracked using this object
struct monad_event_ring_control
{
    alignas(64) uint64_t last_seqno; ///< Last seq. number allocated by writer
    uint64_t next_payload_byte;      ///< Next payload buffer byte to allocate
    alignas(64) uint64_t buffer_window_start; ///< See event_recorder.md docs
};

/// Event ring shared memory files start with this header structure
struct monad_event_ring_header
{
    struct monad_event_ring_size size;       ///< Size of following structures
    struct monad_event_ring_control control; ///< Tracks ring's state/status
};

// clang-format on

/// Return an initialized event ring size structure, after performing checks
/// on valid size limits; a "shift" is the power-of-2 exponent for a size
int monad_event_ring_init_size(
    uint8_t descriptors_shift, uint8_t payload_buf_shift,
    struct monad_event_ring_size *);

/// Given the size parameters of an event ring, return the total number of
/// bytes needed to store it in memory; can be used to ftruncate(2) a file
/// range large enough to store an event ring
size_t monad_event_ring_calc_storage(struct monad_event_ring_size const *);

/// Initializes an event ring "shared file", to be mmap'ed by multiple
/// processes later. Given an open file descriptor, this creates the event
/// ring data structures at the given offset within that file
int monad_event_ring_init_file(
    struct monad_event_ring_size const *, int ring_fd, off_t ring_offset,
    char const *error_name);

/// Given an open file descriptor which contains an initialized event ring at
/// `ring_offset`, mmap the event ring into our address space; mmap_extra_flags
/// is OR'ed with MAP_SHARED to produce the final flags
int monad_event_ring_mmap(
    struct monad_event_ring *, int mmap_prot, int mmap_extra_flags, int ring_fd,
    off_t ring_offset, char const *error_name);

/// Remove an event ring's shared memory mappings from our process' address
/// space
void monad_event_ring_unmap(struct monad_event_ring *);

/// Initialize an iterator to point to the most recently produced event in the
/// event ring
int monad_event_ring_init_iterator(
    struct monad_event_ring const *, struct monad_event_iterator *);

/// Initialize a recorder to write into an event ring
int monad_event_ring_init_recorder(
    struct monad_event_ring const *, struct monad_event_recorder *);

/// Return a description of the last error that occurred on this thread
char const *monad_event_ring_get_last_error();

/*
 * Event size limits
 */

#define MONAD_EVENT_MIN_DESCRIPTORS_SHIFT (16)
#define MONAD_EVENT_MAX_DESCRIPTORS_SHIFT (32)

#define MONAD_EVENT_MIN_PAYLOAD_BUF_SHIFT (27)
#define MONAD_EVENT_MAX_PAYLOAD_BUF_SHIFT (40)

#ifdef __cplusplus
} // extern "C"
#endif
