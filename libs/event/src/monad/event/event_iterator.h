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
    MONAD_EVENT_PARTIAL,
    MONAD_EVENT_GAP
};

/*
 * Zero-copy style APIs
 */

/// Obtain a pointer to the next event in a zero-copy fashion, if one is
/// available
static enum monad_event_poll_result monad_event_iterator_peek(
    struct monad_event_iterator *, struct monad_event_fragment const **begin,
    struct monad_event_fragment const **end);

/// Advance to the next event, returning true only if the consumed event was
/// still valid immediately before advancing past it. Note that if false is
/// returned, a gap has already occurred, or is almost certainly about to occur
static bool monad_event_iterator_advance(
    struct monad_event_iterator *, struct monad_event_fragment const *begin);

/*
 * Copy-style APIs
 */

/// Copies the event to the provided buffers and advances to the next event if
/// the copy is successful.
static enum monad_event_poll_result monad_event_iterator_copy_next(
    struct monad_event_iterator *, struct monad_event_header *,
    void *payload_buf, size_t payload_buf_size);

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
    struct monad_event_fragment const *fragment_table;
    struct monad_event_fragment const *begin;
    uint64_t scan_seqno;
    uint64_t next_fragment;
    uint64_t last_seqno;
    size_t capacity_mask;
    __uint128_t *seqno_fragment_next;
};

#define MONAD_EVENT_ITERATOR_INTERNAL
#include "event_iterator_inline.h"
#undef MONAD_EVENT_ITERATOR_INTERNAL

#ifdef __cplusplus
} // extern "C"
#endif
