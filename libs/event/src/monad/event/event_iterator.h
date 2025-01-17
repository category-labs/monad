#pragma once

/**
 * @file
 *
 * Defines the basic event iterator object and its API
 */

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_event_iterator;

/// Result of polling the event ring for a new event
enum monad_event_poll_result
{
    MONAD_EVENT_READY,
    MONAD_EVENT_NOT_READY,
    MONAD_EVENT_GAP,
    MONAD_EVENT_PAYLOAD_EXPIRED
};

/// Copies the next event descriptor and advances the iterator, if the next
/// event is available and there is no sequence number gap; otherwise returns a
/// code indicating why no event descriptor was copied
static enum monad_event_poll_result monad_event_iterator_try_next(
    struct monad_event_iterator *, struct monad_event_descriptor *);

/// Copies both the event descriptor and payload to the provided buffers and
/// advances to the next event if both copies are successful.
static enum monad_event_poll_result monad_event_iterator_try_full(
    struct monad_event_iterator *, struct monad_event_descriptor *,
    void *payload_buf, size_t payload_buf_size);

/// Obtain a pointer to the event's payload in shared memory in a zero-copy
/// fashion; to check for expiration, call monad_event_payload_check
static void const *monad_event_payload_peek(
    struct monad_event_iterator const *, struct monad_event_descriptor const *);

/// Returns true if the event payload associated with the given event
/// descriptor is still valid; returns false if it has been overwritten
static bool monad_event_payload_check(
    struct monad_event_iterator const *, struct monad_event_descriptor const *);

/// Copy the event payload from shared memory into the supplied buffer, up to
/// `n` bytes; the total size required for an event is available using the
/// `length` field in the event descriptor; returns nullptr if the event
/// payload's memory has already been reused for a later event
static void *monad_event_payload_memcpy(
    struct monad_event_iterator const *, struct monad_event_descriptor const *,
    void *dst, size_t n);

/// Reset the iterator to point to the latest event produced; used to set the
/// initial iteration point of an open ring, and for "hard" gap recovery
static uint64_t monad_event_iterator_reset(struct monad_event_iterator *);

/// Holds the state of a single event iterator; these are initialized from the
/// imported ring they read from by calling monad_event_imported_ring_init_iter
struct monad_event_iterator
{
    struct monad_event_descriptor const *desc_table;
    uint8_t *payload_buf;
    size_t payload_buf_size;
    size_t capacity_mask;
    uint64_t last_seqno;
    struct monad_event_ring_writer_state const *wr_state;
    uint64_t const *buffer_window_start;
};

#define MONAD_EVENT_ITERATOR_INTERNAL
#include "event_iterator_inline.h"
#undef MONAD_EVENT_ITERATOR_INTERNAL

#ifdef __cplusplus
} // extern "C"
#endif
