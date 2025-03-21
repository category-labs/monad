#pragma once

/**
 * @file
 *
 * Defines the event recorder object and its API; recorders are used for
 * writing events
 */

#include <stddef.h>
#include <stdint.h>

#include <monad/event/event_ring.h>

struct iovec;
struct monad_event_recorder;

#ifdef __cplusplus
extern "C"
{
#endif

/// Reserve resources to record an event; this returns an allocated event
/// descriptor with all fields populated except `seqno` and `event_type`. It
/// sets `ptr` to the start of a payload buffer large enough to hold the
/// `payload_size`. To finish recording, perform an atomic store of the
/// returned `seqno` into the descriptor, with release memory ordering
static struct monad_event_descriptor *monad_event_recorder_reserve(
    struct monad_event_recorder *, size_t payload_size, uint64_t *seqno,
    uint8_t **payload);

/// Take a timestamp, in nanoseconds since the UNIX epoch
static uint64_t monad_event_get_epoch_nanos();

struct monad_event_recorder
{
    struct monad_event_descriptor *descriptors;
    uint8_t *payload_buf;
    struct monad_event_ring_control *control;
    size_t desc_capacity_mask;
    size_t payload_buf_mask;
};

#define MONAD_EVENT_RECORDER_INTERNAL
#include "event_recorder_inline.h"
#undef MONAD_EVENT_RECORDER_INTERNAL

#ifdef __cplusplus
} // extern "C"
#endif
