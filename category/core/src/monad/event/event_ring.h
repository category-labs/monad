#pragma once

/**
 * @file
 *
 * This file contains:
 *
 *   1. Definitions of the event ring's shared memory structures
 *   2. Functions which initialize and mmap event rings
 *   3. Payload buffer access inline functions
 */

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include <sys/types.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_event_descriptor;
struct monad_event_iterator;
struct monad_event_recorder;
struct monad_event_ring_header;

enum monad_event_ring_type : uint16_t;

// clang-format off

/// Describes a shared memory event ring that has been mapped into the address
/// space of the current process
struct monad_event_ring
{
    int mmap_prot;                              ///< Our pages mmap'ed with this
    struct monad_event_ring_header *header;     ///< Event ring metadata
    struct monad_event_descriptor *descriptors; ///< Event descriptor ring array
    uint8_t *payload_buf;                       ///< Payload buffer base address
    void *context_area;                         ///< Ring-specific storage
    uint64_t desc_capacity_mask;                ///< Descriptor capacity - 1
    uint64_t payload_buf_mask;                  ///< Payload buffer size - 1
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
    uint16_t : 16;               ///< Unused tail padding
    uint32_t payload_size;       ///< Size of event payload
    uint64_t record_epoch_nanos; ///< Time event was recorded
    uint64_t payload_buf_offset; ///< Unwrapped offset of payload in p. buf
    uint64_t user[4];            ///< Meaning defined by the writer
};

static_assert(sizeof(struct monad_event_descriptor) == 64);

/// Describes the size of an event ring's primary data structures
struct monad_event_ring_size
{
    size_t descriptor_capacity; ///< # entries in event descriptor array
    size_t payload_buf_size;    ///< Byte size of payload buffer
    size_t context_area_size;   ///< Byte size of context area section
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
    char magic[6];                           ///< 'RINGvv', vv = version number
    enum monad_event_ring_type type;         ///< Kind of event ring this is
    uint8_t metadata_hash[32];               ///< Check that event types match
    struct monad_event_ring_size size;       ///< Size of following structures
    struct monad_event_ring_control control; ///< Tracks ring's state/status
};

/// Describes which event ring an event is recorded to; different categories
/// of events are recorded to different rings, this identifies the integer
/// namespace that the descriptor's `uint16_t event_type` field is drawn from
enum monad_event_ring_type : uint16_t
{
    MONAD_EVENT_RING_TYPE_NONE,  ///< An invalid value
    MONAD_EVENT_RING_TYPE_TEST,  ///< Used in simple automated tests
    MONAD_EVENT_RING_TYPE_COUNT  ///< Total number of known event rings
};

// clang-format on

/// Return an initialized event ring size structure, after performing checks
/// on valid size limits; a "shift" is the power-of-2 exponent for a size
int monad_event_ring_init_size(
    uint8_t descriptors_shift, uint8_t payload_buf_shift,
    uint16_t context_large_pages, struct monad_event_ring_size *);

/// Given the size parameters of an event ring, return the total number of
/// bytes needed to store it in memory; can be used to ftruncate(2) a file
/// range large enough to store an event ring
size_t monad_event_ring_calc_storage(struct monad_event_ring_size const *);

/// Initializes an event ring "shared file", to be mmap'ed by multiple
/// processes later. Given an open file descriptor, this creates the event
/// ring data structures at the given offset within that file
int monad_event_ring_init_file(
    struct monad_event_ring_size const *, enum monad_event_ring_type,
    uint8_t const *metadata_hash, int ring_fd, off_t ring_offset,
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

/// Try to copy the event descriptor corresponding to a particular sequence
/// number; returns true only if the descriptor was available and its contents
/// were copied into the descriptor output buffer
static bool monad_event_ring_try_copy(
    struct monad_event_ring const *, uint64_t seqno,
    struct monad_event_descriptor *);

/// Obtain a pointer to the event's payload in shared memory in a zero-copy
/// fashion; to check for expiration, call monad_event_payload_check
static void const *monad_event_ring_payload_peek(
    struct monad_event_ring const *, struct monad_event_descriptor const *);

/// Return true if the zero-copy buffer returned by monad_event_payload_peek
/// still contains the event payload for the given descriptor; returns false if
/// the event payload has been overwritten
static bool monad_event_ring_payload_check(
    struct monad_event_ring const *, struct monad_event_descriptor const *);

/// Copy the event payload from shared memory into the supplied buffer, up to
/// `n` bytes; returns nullptr if the event payload has been overwritten
static void *monad_event_ring_payload_memcpy(
    struct monad_event_ring const *, struct monad_event_descriptor const *,
    void *dst, size_t n);

/// Initialize an iterator to point to the most recently produced event in the
/// event ring
int monad_event_ring_init_iterator(
    struct monad_event_ring const *, struct monad_event_iterator *);

/// Initialize a recorder to write into an event ring
int monad_event_ring_init_recorder(
    struct monad_event_ring const *, struct monad_event_recorder *);

/// Return a description of the last error that occurred on this thread
char const *monad_event_ring_get_last_error();

/// This should be changed whenever anything binary-affecting in this file
/// changes (e.g., any structure or enumeration value that is shared memory
/// resident, e.g., `enum monad_event_ring_type`)
constexpr uint8_t MONAD_EVENT_RING_HEADER_VERSION[] = {
    'R', 'I', 'N', 'G', '0', '1'};

/// Array of human-readable names for the event ring types
extern char const *g_monad_event_ring_type_names[MONAD_EVENT_RING_TYPE_COUNT];

/*
 * Event ring size limits
 */

constexpr uint8_t MONAD_EVENT_MIN_DESCRIPTORS_SHIFT = 16;
constexpr uint8_t MONAD_EVENT_MAX_DESCRIPTORS_SHIFT = 32;

constexpr uint8_t MONAD_EVENT_MIN_PAYLOAD_BUF_SHIFT = 27;
constexpr uint8_t MONAD_EVENT_MAX_PAYLOAD_BUF_SHIFT = 40;

/*
 * Event ring inline function definitions
 */

inline bool monad_event_ring_try_copy(
    struct monad_event_ring const *event_ring, uint64_t seqno,
    struct monad_event_descriptor *event)
{
    if (__builtin_expect(seqno == 0, 0)) {
        return false;
    }
    struct monad_event_descriptor const *const ring_event =
        &event_ring->descriptors[(seqno - 1) & event_ring->desc_capacity_mask];
    *event = *ring_event;
    uint64_t const ring_seqno =
        __atomic_load_n(&ring_event->seqno, __ATOMIC_ACQUIRE);
    if (__builtin_expect(ring_seqno != seqno, 0)) {
        return false;
    }
    return true;
}

inline void const *monad_event_ring_payload_peek(
    struct monad_event_ring const *event_ring,
    struct monad_event_descriptor const *event)
{
    return event_ring->payload_buf +
           (event->payload_buf_offset & event_ring->payload_buf_mask);
}

inline bool monad_event_ring_payload_check(
    struct monad_event_ring const *event_ring,
    struct monad_event_descriptor const *event)
{
    return event->payload_buf_offset >=
           __atomic_load_n(
               &event_ring->header->control.buffer_window_start,
               __ATOMIC_ACQUIRE);
}

inline void *monad_event_ring_payload_memcpy(
    struct monad_event_ring const *event_ring,
    struct monad_event_descriptor const *event, void *dst, size_t n)
{
    if (__builtin_expect(
            !monad_event_ring_payload_check(event_ring, event), 0)) {
        return nullptr;
    }
    void const *const src = monad_event_ring_payload_peek(event_ring, event);
    memcpy(dst, src, n);
    if (__builtin_expect(
            !monad_event_ring_payload_check(event_ring, event), 0)) {
        return nullptr; // Payload expired
    }
    return dst;
}

#ifdef __cplusplus
} // extern "C"
#endif
