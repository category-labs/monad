/**
 * @file
 *
 * This file contains the implementation of the event iterator API, which is
 * entirely inlined for performance reasons.
 */

#ifndef MONAD_EVENT_ITERATOR_INTERNAL
    #error This file should only be included directly by event_iterator.h
#endif

#include <assert.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include <monad/event/event.h>

static inline uint64_t
monad_event_iterator_sync_wait(struct monad_event_iterator *iter)
{
    uint64_t last_seqno;
    struct monad_event_descriptor const *event;
    __atomic_load(&iter->wr_state->last_seqno, &last_seqno, __ATOMIC_ACQUIRE);
    if (__builtin_expect(last_seqno == 0, 0)) {
        // Nothing materialized anyway
        // TODO(ken): should it be an error if this happens? assert instead?
        return iter->last_seqno = 0;
    }
    // `last_seqno` is the last sequence number the event ring writer has
    // allocated. The writer may still be in the process of recording the
    // event associated with the sequence number, so it may not be safe
    // to read its event descriptor yet.
    //
    // It is safe to read when the sequence number is atomically stored into
    // the associated descriptor table slot (which is `last_seqno - 1`)
    // with memory_order_release ordering. This waits for that to happen, if it
    // hasn't yet.
    event = &iter->desc_table[(last_seqno - 1) & iter->capacity_mask];
    while (atomic_load_explicit(&event->seqno, memory_order_acquire) <
           last_seqno)
        /*empty*/;
    return last_seqno;
}

inline enum monad_event_poll_result monad_event_iterator_peek(
    struct monad_event_iterator *iter,
    struct monad_event_descriptor const **event)
{
    *event = &iter->desc_table[iter->last_seqno & iter->capacity_mask];
    uint64_t const seqno =
        atomic_load_explicit(&(*event)->seqno, memory_order_acquire);
    if (__builtin_expect(seqno == iter->last_seqno + 1, 1)) {
        return MONAD_EVENT_READY;
    }
    return seqno < iter->last_seqno ? MONAD_EVENT_NOT_READY : MONAD_EVENT_GAP;
}

inline bool monad_event_iterator_advance(struct monad_event_iterator *iter)
{
    struct monad_event_descriptor const *const event =
        &iter->desc_table[iter->last_seqno & iter->capacity_mask];
    uint64_t const seqno =
        atomic_load_explicit(&event->seqno, memory_order_acquire);
    if (__builtin_expect(seqno == iter->last_seqno + 1, 1)) {
        ++iter->last_seqno;
        return true;
    }
    return false;
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

inline enum monad_event_poll_result monad_event_iterator_copy_next(
    struct monad_event_iterator *iter, struct monad_event_descriptor *event_dst,
    void *payload_buf, size_t payload_buf_size)
{
    uint64_t seqno;
    size_t copy_size;

    struct monad_event_descriptor const *const event_src =
        &iter->desc_table[iter->last_seqno & iter->capacity_mask];
#if defined(__cplusplus) && !defined(__clang__)
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Wclass-memaccess"
#endif
    memcpy(event_dst, event_src, sizeof *event_dst);
#if defined(__cplusplus) && !defined(__clang__)
    #pragma GCC diagnostic pop
#endif
    seqno = atomic_load_explicit(&event_dst->seqno, memory_order_relaxed);
    if (__builtin_expect(
            seqno !=
                atomic_load_explicit(&event_src->seqno, memory_order_acquire),
            0)) {
        return MONAD_EVENT_GAP;
    }
    if (__builtin_expect(seqno == iter->last_seqno + 1, 1)) {
        copy_size = payload_buf_size > event_dst->length ? event_dst->length
                                                         : payload_buf_size;
        if (__builtin_expect(
                monad_event_payload_memcpy(
                    iter, event_dst, payload_buf, copy_size) == nullptr,
                0)) {
            return MONAD_EVENT_PAYLOAD_EXPIRED;
        }
        (void)monad_event_iterator_advance(iter);
        return MONAD_EVENT_READY;
    }
    return seqno < iter->last_seqno ? MONAD_EVENT_NOT_READY : MONAD_EVENT_GAP;
}

inline void *monad_event_payload_memcpy(
    struct monad_event_iterator const *iter,
    struct monad_event_descriptor const *event, void *dst, size_t n)
{
    void const *const src = monad_event_payload_peek(iter, event);
    memcpy(dst, src, n);
    if (__builtin_expect(!monad_event_payload_check(iter, event), 0)) {
        // The bytes of this event were reused by a later event that overwrote
        // it (we didn't copy this fast enough to be sure that all
        // `n` bytes are valid).
        return nullptr;
    }
    return dst;
}

inline uint64_t monad_event_iterator_reset(struct monad_event_iterator *iter)
{
    return iter->last_seqno = monad_event_iterator_sync_wait(iter);
}
