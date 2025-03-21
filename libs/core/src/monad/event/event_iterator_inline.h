/**
 * @file
 *
 * This file contains the implementation of the event iterator API, which is
 * entirely inlined for performance reasons. To understand this code, read the
 * section "Sequence numbers and the lifetime detection algorithm" in the
 * `event.md` documentation file.
 */

#ifndef MONAD_EVENT_ITERATOR_INTERNAL
    #error This file should only be included directly by event_iterator.h
#endif

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include <monad/event/event_ring.h>

static inline uint64_t
monad_event_iterator_sync_wait(struct monad_event_iterator *iter)
{
    struct monad_event_descriptor const *event;
    uint64_t const write_last_seqno =
        __atomic_load_n(&iter->control->last_seqno, __ATOMIC_ACQUIRE);
    if (__builtin_expect(write_last_seqno == 0, 0)) {
        // Nothing materialized anyway
        return 0;
    }
    // `write_last_seqno` is the last sequence number the writer has allocated.
    // The writer may still be in the process of recording the event associated
    // with that sequence number, so it may not be safe to read this event
    // descriptor's fields yet.
    //
    // It is safe to read when the sequence number is atomically stored into
    // the associated descriptor array slot (which is `write_last_seqno - 1`)
    // with release memory ordering. This waits for that to happen, if it
    // hasn't yet.
    event =
        &iter->descriptors[(write_last_seqno - 1) & iter->desc_capacity_mask];
    while (__atomic_load_n(&event->seqno, __ATOMIC_ACQUIRE) <
           write_last_seqno) {
#if defined(__x86_64__)
        __builtin_ia32_pause();
#endif
    }
    return write_last_seqno;
}

inline enum monad_event_next_result monad_event_iterator_try_next(
    struct monad_event_iterator *iter, struct monad_event_descriptor *event)
{
    struct monad_event_descriptor const *const ring_event =
        &iter->descriptors[iter->read_last_seqno & iter->desc_capacity_mask];
    uint64_t const seqno =
        __atomic_load_n(&ring_event->seqno, __ATOMIC_ACQUIRE);
    if (__builtin_expect(seqno == iter->read_last_seqno + 1, 1)) {
        // Copy the structure, then reload sequence number with
        // __ATOMIC_ACQUIRE to make sure it still matches after the copy
        *event = *ring_event;
        __atomic_load(&ring_event->seqno, &event->seqno, __ATOMIC_ACQUIRE);
        if (__builtin_expect(event->seqno == seqno, 1)) {
            ++iter->read_last_seqno;
            return MONAD_EVENT_SUCCESS;
        }
        return MONAD_EVENT_GAP;
    }
    if (__builtin_expect(seqno < iter->read_last_seqno, 1)) {
        return MONAD_EVENT_NOT_READY;
    }
    return seqno == iter->read_last_seqno && seqno == 0 ? MONAD_EVENT_NOT_READY
                                                        : MONAD_EVENT_GAP;
}

inline void const *monad_event_payload_peek(
    struct monad_event_iterator const *iter,
    struct monad_event_descriptor const *event)
{
    return iter->payload_buf +
           (event->payload_buf_offset & iter->payload_buf_mask);
}

inline bool monad_event_payload_check(
    struct monad_event_iterator const *iter,
    struct monad_event_descriptor const *event)
{
    return event->payload_buf_offset >=
           __atomic_load_n(
               &iter->control->buffer_window_start, __ATOMIC_ACQUIRE);
}

inline void *monad_event_payload_memcpy(
    struct monad_event_iterator const *iter,
    struct monad_event_descriptor const *event, void *dst, size_t n)
{
    if (__builtin_expect(!monad_event_payload_check(iter, event), 0)) {
        return nullptr;
    }
    void const *const src = monad_event_payload_peek(iter, event);
    memcpy(dst, src, n);
    if (__builtin_expect(!monad_event_payload_check(iter, event), 0)) {
        return nullptr; // Payload expired
    }
    return dst;
}

inline uint64_t monad_event_iterator_reset(struct monad_event_iterator *iter)
{
    return iter->read_last_seqno = monad_event_iterator_sync_wait(iter);
}
