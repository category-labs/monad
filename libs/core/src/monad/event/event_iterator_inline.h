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

#include <monad/event/event.h>

static inline uint64_t
monad_event_iterator_sync_wait(struct monad_event_iterator *iter)
{
    uint64_t last_seqno;
    struct monad_event_descriptor const *event;
    __atomic_load(iter->write_last_seqno, &last_seqno, __ATOMIC_ACQUIRE);
    if (__builtin_expect(last_seqno == 0, 0)) {
        // Nothing materialized anyway
        return 0;
    }
    // `last_seqno` is the last sequence number the writer has allocated. The
    // writer may still be in the process of recording the event associated
    // with that sequence number, so it may not be safe to read this event
    // descriptor's fields yet.
    //
    // It is safe to read when the sequence number is atomically stored into
    // the associated descriptor array slot (which is `last_seqno - 1`)
    // with release memory ordering. This waits for that to happen, if it
    // hasn't yet.
    event = &iter->descriptors[(last_seqno - 1) & iter->desc_capacity_mask];
    while (__atomic_load_n(&event->seqno, __ATOMIC_ACQUIRE) < last_seqno) {
#if defined(__x86_64__)
        __builtin_ia32_pause();
#endif
    }
    return last_seqno;
}

inline void monad_event_iterator_init(
    struct monad_event_iterator *iter,
    struct monad_event_ring const *event_ring)
{
    memset(iter, 0, sizeof *iter);
    iter->descriptors = event_ring->descriptors;
    iter->desc_capacity_mask = event_ring->header->descriptor_capacity - 1;
    iter->payload_buf = event_ring->payload_buf;
    iter->payload_buf_size = event_ring->header->payload_buf_size;
    iter->write_last_seqno = &event_ring->header->control.last_seqno;
    iter->buffer_window_start =
        &event_ring->header->control.buffer_window_start;
    (void)monad_event_iterator_reset(iter);
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
    return event->inline_payload
               ? event->payload
               : iter->payload_buf +
                     (event->payload_buf_offset & (iter->payload_buf_size - 1));
}

inline bool monad_event_payload_check(
    struct monad_event_iterator const *iter,
    struct monad_event_descriptor const *event)
{
    return event->inline_payload ||
           event->payload_buf_offset >=
               __atomic_load_n(iter->buffer_window_start, __ATOMIC_ACQUIRE);
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

inline enum monad_event_next_result monad_event_iterator_try_copy_all(
    struct monad_event_iterator *iter, struct monad_event_descriptor *event,
    void *payload_buf, size_t payload_buf_size)
{
    enum monad_event_next_result const nr =
        monad_event_iterator_try_next(iter, event);
    if (__builtin_expect(nr != MONAD_EVENT_SUCCESS, 0)) {
        return nr;
    }
    size_t const copy_size =
        payload_buf_size > event->length ? event->length : payload_buf_size;
    return monad_event_payload_memcpy(iter, event, payload_buf, copy_size) !=
                   nullptr
               ? MONAD_EVENT_SUCCESS
               : MONAD_EVENT_PAYLOAD_EXPIRED;
}

inline uint64_t monad_event_iterator_reset(struct monad_event_iterator *iter)
{
    return iter->read_last_seqno = monad_event_iterator_sync_wait(iter);
}
