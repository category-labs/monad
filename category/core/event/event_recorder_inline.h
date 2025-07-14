/**
 * @file
 *
 * This file defines routines for the event recorder that must be inlined
 * for the sake of performance.
 */

#ifndef MONAD_EVENT_RECORDER_INTERNAL
    #error This file should only be included directly by event_recorder.h
#endif

#include <stdbit.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#include <sys/types.h>

#include <category/core/likely.h>
#include <category/core/event/event_ring.h>
#include <category/core/mem/align.h>

#ifdef __cplusplus
extern "C"
{
#endif

/*
 * Inline function definitions
 */

inline uint64_t monad_event_get_epoch_nanos()
{
    struct timespec now;
    (void)clock_gettime(CLOCK_REALTIME, &now);
    return (uint64_t)(now.tv_sec * 1'000'000'000L + now.tv_nsec);
}

// Reserve the shared memory resources needed to record the next event for
// in an event ring; this does the following:
//
//   - allocates a sequence number for the event; doing this also causes a slot
//     to be reserved in the descriptor array to hold an event's descriptor,
//     since the array index and sequence number are related by the
//     equation `array_index = (seqno - 1) % capacity`
//
//   - allocates space in the payload buffer for the event payload
//
//   - fills in the event descriptor fields that relate to the payload and
//     timestamp
//
// This returns a pointer to the allocated slot in the event ring, the
// allocated sequence number, and the space to copy the event payload. When
// the user is finished copying the payload, at atomic store of `seqno` into
// the descriptor will finish the recording process.
static inline struct monad_event_descriptor *monad_event_recorder_reserve(
    struct monad_event_recorder *recorder, size_t payload_size, uint64_t *seqno,
    uint8_t **payload)
{
    struct monad_event_descriptor *event;
    uint64_t buffer_window_start;
    uint64_t payload_begin;
    uint64_t payload_end;
    uint64_t const WINDOW_INCR = 1UL << 24;

    uint64_t const start_record_timestamp = monad_event_get_epoch_nanos();
    struct monad_event_ring_control *const rctl = recorder->control;
    size_t const alloc_size = monad_round_size_to_align(payload_size, 8);

    // Allocate the sequence number and payload buffer bytes
    uint64_t const last_seqno =
        __atomic_fetch_add(&rctl->last_seqno, 1, __ATOMIC_RELAXED);
    payload_begin = __atomic_fetch_add(
        &rctl->next_payload_byte, alloc_size, __ATOMIC_RELAXED);

    // We're going to start filling in the fields of `event`. Overwrite its
    // sequence number to zero, in case this slot is occupied by an older event
    // and that older event is currently being examined by a reading thread.
    // This ensures the reader can always detect that fields are invalidated.
    event = &recorder->descriptors[last_seqno & recorder->desc_capacity_mask];
    __atomic_store_n(&event->seqno, 0, __ATOMIC_RELEASE);

    // Check if we need to move the sliding buffer window
    payload_end = payload_begin + alloc_size;
    buffer_window_start =
        __atomic_load_n(&rctl->buffer_window_start, __ATOMIC_RELAXED);
    if (MONAD_UNLIKELY(
            payload_end - buffer_window_start >
            recorder->payload_buf_mask + 1 - WINDOW_INCR)) {
        // Slide the buffer window over by the payload size, rounded up to the
        // nearest `WINDOW_INCR`, see the "Sliding buffer window" section in
        // `event_recorder.md`
        __atomic_compare_exchange_n(
            &rctl->buffer_window_start,
            &buffer_window_start,
            buffer_window_start +
                monad_round_size_to_align(payload_size, WINDOW_INCR),
            false,
            __ATOMIC_RELAXED,
            __ATOMIC_RELAXED);
    }

    event->payload_size = (uint32_t)payload_size;
    event->payload_buf_offset = payload_begin;
    event->record_epoch_nanos = start_record_timestamp;
    *seqno = last_seqno + 1;
    *payload =
        &recorder->payload_buf[payload_begin & recorder->payload_buf_mask];

    return event;
}

inline void monad_event_recorder_commit(
    struct monad_event_descriptor *event, uint64_t seqno)
{
    __atomic_store_n(&event->seqno, seqno, __ATOMIC_RELEASE);
}

#ifdef __cplusplus
} // extern "C"
#endif
