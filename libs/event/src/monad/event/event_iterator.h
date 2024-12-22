#pragma once

/**
 * @file
 *
 * Defines the basic event iterator object and its API
 */

#include <stdatomic.h>
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

/*
 * Zero-copy style APIs
 */

/// Obtain a pointer to the next event descriptor in a zero-copy fashion,
/// if one is available
static enum monad_event_poll_result monad_event_iterator_peek(
    struct monad_event_iterator *, struct monad_event_descriptor const **);

/// Advance to the next event, returning true only if the consumed event was
/// still valid immediately before advancing past it. Note that if false is
/// returned, a gap has already occurred, or is almost certainly about to occur
static bool monad_event_iterator_advance(struct monad_event_iterator *);

/// Obtain a pointer to the event's payload in shared memory in a zero-copy
/// fashion
static void const *monad_event_payload_peek(
    struct monad_event_iterator const *, struct monad_event_descriptor const *,
    _Atomic(uint64_t) const **page_overwrite_seqno);

/*
 * Copy-style APIs
 */

/// Copies both the event descriptor and payload to the provided buffers and
/// advances to the next event if both copies are successful.
static enum monad_event_poll_result monad_event_iterator_copy_next(
    struct monad_event_iterator *, struct monad_event_descriptor *,
    void *payload_buf, size_t payload_buf_size);

/// Copy `num_events` event descriptors into the array pointed by `events`;
/// `num_events` initially contains the size of the `events` array, and upon
/// return contains the number of events copied. If `num_available_events` is
/// not nullptr, the number of events that were available (which might be
/// larger than `num_events`) will be copied out, which can be used to detect
/// back-pressure
static enum monad_event_poll_result monad_event_iterator_bulk_copy(
    struct monad_event_iterator *, struct monad_event_descriptor *events,
    size_t *num_events, size_t *num_available_events);

/// Copy the event payload from shared memory into the supplied buffer, up to
/// `n` bytes; the total size required for an event is available using the
/// `length` field in the event descriptor; returns nullptr if the event
/// payload's memory has already been reused for a later event
static void *monad_event_payload_memcpy(
    struct monad_event_iterator const *, struct monad_event_descriptor const *,
    void *dst, size_t n);

/*
 * Other iterator APIs
 */

/// Reset the iterator to point to the latest event produced; used to set the
/// initial iteration point of an open ring, and for "hard" gap recovery
static uint64_t monad_event_iterator_reset(struct monad_event_iterator *);

/// Holds the state of a single event iterator; these are initialized
/// from the imported ring they read from using
/// monad_event_imported_ring_init_iter
struct monad_event_iterator
{
    struct monad_event_descriptor const *desc_table;
    struct monad_event_payload_page const **payload_pages;
    uint64_t last_seqno;
    size_t capacity_mask;
    _Atomic(uint64_t) *prod_next;
};

#define MONAD_EVENT_ITERATOR_INTERNAL
#include "event_iterator_inline.h"
#undef MONAD_EVENT_ITERATOR_INTERNAL

#ifdef __cplusplus
} // extern "C"
#endif
