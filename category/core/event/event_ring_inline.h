// Copyright (C) 2025-26 Category Labs, Inc.
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

#ifndef MONAD_EVENT_RING_INTERNAL
    #error This file should only be included directly by event_ring.h
#endif

/**
 * @file
 *
 * This file contains the implementation of the event ring API, which is
 * entirely inlined for performance reasons. To understand this code, read the
 * section "Sequence numbers and the lifetime detection algorithm" in the
 * "Advanced topics" section of the SDK documentation.
 */

#include <category/core/event/event_def.h>
#include <category/core/likely.h>

inline monad_event_ring_result_t monad_event_ring_try_copy(
    struct monad_event_ring const *const event_ring, uint64_t const seqno,
    struct monad_event_descriptor *const event_buf)
{
    if (MONAD_UNLIKELY(seqno == 0)) {
        // Zero is not a valid sequence number, but we return NOT_READY if they
        // try to read it. This gives reasonable defined behavior to reading
        // from an iterator at the "current position," in an event ring which
        // has not yet recorded anything (the iterator is conceptually
        // positioned at "before the beginning")
        return MONAD_EVENT_RING_NOT_READY;
    }
    struct monad_event_descriptor const *const ring_event =
        &event_ring->descriptors[(seqno - 1) & event_ring->desc_capacity_mask];
    uint64_t const ring_seqno =
        __atomic_load_n(&ring_event->seqno, __ATOMIC_ACQUIRE);
    if (MONAD_LIKELY(ring_seqno == seqno)) {
        // Copy the structure, then reload the sequence number with
        // __ATOMIC_ACQUIRE to make sure it still matches after the copy
        *event_buf = *ring_event;
        __atomic_load(&ring_event->seqno, &event_buf->seqno, __ATOMIC_ACQUIRE);
        if (MONAD_LIKELY(event_buf->seqno == seqno)) {
            return MONAD_EVENT_RING_SUCCESS;
        }
        return MONAD_EVENT_RING_GAP;
    }
    if (MONAD_LIKELY(ring_seqno < seqno)) {
        return MONAD_EVENT_RING_NOT_READY;
    }
    return MONAD_EVENT_RING_GAP;
}

inline void const *monad_event_ring_payload_peek(
    struct monad_event_ring const *const event_ring,
    struct monad_event_descriptor const *const event)
{
    return event_ring->payload_buf +
           (event->payload_buf_offset & event_ring->payload_buf_mask);
}

inline bool monad_event_ring_payload_check(
    struct monad_event_ring const *const event_ring,
    struct monad_event_descriptor const *const event)
{
    return event->payload_buf_offset >=
           __atomic_load_n(
               &event_ring->header->control.buffer_window_start,
               __ATOMIC_ACQUIRE);
}

inline void *monad_event_ring_payload_memcpy(
    struct monad_event_ring const *const event_ring,
    struct monad_event_descriptor const *const event, void *const dst,
    size_t const n)
{
    if (MONAD_UNLIKELY(!monad_event_ring_payload_check(event_ring, event))) {
        return nullptr;
    }
    void const *const src = monad_event_ring_payload_peek(event_ring, event);
    memcpy(dst, src, n);
    if (MONAD_UNLIKELY(!monad_event_ring_payload_check(event_ring, event))) {
        return nullptr; // Payload expired
    }
    return dst;
}

inline uint64_t monad_event_ring_get_last_written_seqno(
    struct monad_event_ring const *const event_ring, bool const sync_wait)
{
    constexpr uint64_t MAX_SYNC_SPIN = 100;
    uint64_t write_last_seqno = __atomic_load_n(
        &event_ring->header->control.last_seqno, __ATOMIC_ACQUIRE);
    if (!sync_wait) {
        return write_last_seqno;
    }
    // `write_last_seqno` is the last sequence number the writer has allocated.
    // The writer may still be in the process of recording the event associated
    // with that sequence number, so it may not be safe to read this event
    // descriptor's fields yet.
    //
    // It is safe to read when the sequence number is atomically stored into
    // the associated descriptor array slot (which is `write_last_seqno - 1`)
    // with release memory ordering. This waits for that to happen, if it
    // hasn't yet. If the process died unexpectedly before finalizing the write
    // (or if we read from the wrong slot in a debugging scenario) then the
    // loop will never terminate, so we scan backwards if it doesn't appear
    // that the operation is finalizing.
    while (write_last_seqno > 0) {
        uint64_t spin_counter = 0;
        size_t const index =
            (write_last_seqno - 1) & event_ring->desc_capacity_mask;
        struct monad_event_descriptor const *event =
            &event_ring->descriptors[index];
        while (__atomic_load_n(&event->seqno, __ATOMIC_ACQUIRE) !=
                   write_last_seqno &&
               spin_counter++ < MAX_SYNC_SPIN) {
#if defined(__x86_64__)
            __builtin_ia32_pause();
#endif
        }
        if (__atomic_load_n(&event->seqno, __ATOMIC_ACQUIRE) ==
            write_last_seqno) {
            return write_last_seqno;
        }
        --write_last_seqno;
    }
    return 0;
}
