#pragma once

/**
 * @file
 *
 * Defines the event iterator object and its API; iterators are used for
 * reading events
 */

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_event_descriptor;
struct monad_event_iterator;
struct monad_event_ring_control;

// clang-format off

/// Result of trying to atomically read the next available event and advance
/// the iterator past it
enum monad_event_next_result
{
    MONAD_EVENT_SUCCESS,         ///< Event read and iterator advanced
    MONAD_EVENT_NOT_READY,       ///< No events are available right now
    MONAD_EVENT_GAP              ///< Sequence number gap detected; not advanced
};

// clang-format on

/// Copy the next event descriptor and advance the iterator, if the next event
/// is available; returns MONAD_EVENT_SUCCESS upon success, otherwise returns
/// a code indicating why the iterator could not be advanced
static enum monad_event_next_result monad_event_iterator_try_next(
    struct monad_event_iterator *, struct monad_event_descriptor *);

/// Obtain a pointer to the event's payload in shared memory in a zero-copy
/// fashion; to check for expiration, call monad_event_payload_check
static void const *monad_event_payload_peek(
    struct monad_event_iterator const *, struct monad_event_descriptor const *);

/// Return true if the zero-copy buffer returned by monad_event_payload_peek
/// still contains the event payload for the given descriptor; returns false if
/// the event payload has been overwritten
static bool monad_event_payload_check(
    struct monad_event_iterator const *, struct monad_event_descriptor const *);

/// Copy the event payload from shared memory into the supplied buffer, up to
/// `n` bytes; returns nullptr if the event payload has been overwritten
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
    uint64_t read_last_seqno;
    struct monad_event_descriptor const *descriptors;
    uint8_t const *payload_buf;
    size_t desc_capacity_mask;
    size_t payload_buf_mask;
    struct monad_event_ring_control const *control;
};

// clang-format on

#define MONAD_EVENT_ITERATOR_INTERNAL
#include "event_iterator_inline.h"
#undef MONAD_EVENT_ITERATOR_INTERNAL

#ifdef __cplusplus
} // extern "C"
#endif
