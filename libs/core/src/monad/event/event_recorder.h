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

/// Record an event whose payload is in a single contiguous buffer
static void monad_event_record(
    struct monad_event_recorder *, uint16_t event_type, void const *payload,
    size_t payload_size);

/// Record an event with "gather I/O", similar to writev(2)
static void monad_event_recordv(
    struct monad_event_recorder *, uint16_t event_type, struct iovec const *iov,
    size_t iovlen);

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
