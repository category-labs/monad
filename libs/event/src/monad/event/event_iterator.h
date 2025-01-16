#pragma once

/**
 * @file
 *
 * Defines the event iterator object and its API
 */

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_event_iterator;
struct monad_event_ring;

// clang-format off

/// Result of trying to atomically read the next available event and advance
/// the iterator past it
enum monad_event_next_result
{
    MONAD_EVENT_SUCCESS,         ///< Event read and iterator advanced
    MONAD_EVENT_NOT_READY,       ///< No events are available right now
    MONAD_EVENT_GAP,             ///< Sequence number gap detected; not advanced
    MONAD_EVENT_PAYLOAD_EXPIRED  ///< Iterator advanced, but payload is expired
};

// clang-format on

/// Initialize an iterator to point to the most recently produced event in the
/// event ring
static void monad_event_iterator_init(
    struct monad_event_iterator *, struct monad_event_ring const *);

/// Copy the next event descriptor and advance the iterator, if the next event
/// is available; returns MONAD_EVENT_SUCCESS upon success, otherwise returns
/// a code indicating why the iterator could not be advanced
static enum monad_event_next_result monad_event_iterator_try_next(
    struct monad_event_iterator *, struct monad_event_descriptor *);

/// Copy both the event descriptor and payload to the provided buffers and
/// advance to the next event, if both copies are successful
static enum monad_event_next_result monad_event_iterator_try_copy_all(
    struct monad_event_iterator *, struct monad_event_descriptor *,
    void *payload_buf, size_t payload_buf_size);

/// Obtain a pointer to the event's payload in shared memory in a zero-copy
/// fashion; to check for expiration, call monad_event_payload_check
static void const *monad_event_payload_peek(
    struct monad_event_iterator const *, struct monad_event_descriptor const *);

/// Return true if the event payload associated with the given event descriptor
/// is still valid (this returns false if the payload has been overwritten)
static bool monad_event_payload_check(
    struct monad_event_iterator const *, struct monad_event_descriptor const *);

/// Copy the event payload from shared memory into the supplied buffer, up to
/// `n` bytes; the total size required for an event is available using the
/// `length` field in the event descriptor; returns nullptr if the event
/// payload has expired (i.e., its memory has been reused by a later event)
static void *monad_event_payload_memcpy(
    struct monad_event_iterator const *, struct monad_event_descriptor const *,
    void *dst, size_t n);

/// Reset the iterator to point to the latest event produced; used for gap
/// recovery
static uint64_t monad_event_iterator_reset(struct monad_event_iterator *);

// clang-format off

/// Holds the state of a single event iterator
struct monad_event_iterator
{
    struct monad_event_descriptor const
        *descriptors;                    ///< Event descriptor ring array
    size_t capacity_mask;                ///< Descriptor array capacity - 1
    uint64_t read_last_seqno;            ///< Seq. number of last event we read
    uint8_t *payload_buf;                ///< Event payload byte buffer
    size_t payload_buf_size;             ///< Size of payload buffer
    uint64_t const *write_last_seqno;    ///< Seq. number of last written event
    uint64_t const *buffer_window_start; ///< Buffer window start (see event.md)
};

// clang-format on

#define MONAD_EVENT_ITERATOR_INTERNAL
#include "event_iterator_inline.h"
#undef MONAD_EVENT_ITERATOR_INTERNAL

#ifdef __cplusplus
} // extern "C"
#endif
