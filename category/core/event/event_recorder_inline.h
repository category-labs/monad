// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

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

#include <category/core/event/event_ring.h>
#include <category/core/likely.h>
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

    uint64_t const start_record_timestamp = monad_event_get_epoch_nanos();
    uint64_t const payload_buf_size = recorder->payload_buf_mask + 1;
    uint64_t const sliding_window_width =
        payload_buf_size - MONAD_EVENT_WINDOW_INCR;
    struct monad_event_ring_control *const rctl = recorder->control;
    size_t const alloc_size = monad_round_size_to_align(payload_size, 8);

    if (MONAD_UNLIKELY(alloc_size > UINT32_MAX)) {
        *seqno = 0;
        *payload = nullptr;
        return nullptr;
    }

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
            payload_end - buffer_window_start > sliding_window_width)) {
        // Slide the buffer window over to the end of the payload rounded up to
        // the nearest `WINDOW_INCR`; see the "Sliding buffer window" section
        // in `event_recorder.md`
        __atomic_compare_exchange_n(
            &rctl->buffer_window_start,
            &buffer_window_start,
            monad_round_size_to_align(payload_end, MONAD_EVENT_WINDOW_INCR) -
                sliding_window_width,
            false,
            __ATOMIC_RELAXED,
            __ATOMIC_RELAXED);
    }

    // 32-bit truncation of `payload_size` is safe because of the earlier
    // UINT32_MAX overflow check
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
