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
monad_event_iterator_sync_wait(struct monad_event_iterator *iterator)
{
    struct monad_event_descriptor const *event;
    uint64_t const prod_next =
        atomic_load_explicit(iterator->prod_next, memory_order_acquire);
    if (__builtin_expect(prod_next == 0, 0)) {
        // Nothing materialized anyway
        // TODO(ken): it is always an error if this happens? assert instead?
        return iterator->last_seqno = 0;
    }
    // `prod_next` is atomically incremented before the contents of the
    // associated descriptor table slot (which is `prod_next - 1`) are written.
    // The contents are definitely commited when the sequence number (which is
    // equal to `prod_next`) is atomically stored (with memory_order_release).
    // This waits for that to happen, if it hasn't.
    event = &iterator->desc_table[(prod_next - 1) & iterator->capacity_mask];
    while (atomic_load_explicit(&event->seqno, memory_order_acquire) <
           prod_next)
        /*empty*/;
    return prod_next - 1;
}

inline enum monad_event_poll_result monad_event_iterator_peek(
    struct monad_event_iterator *iterator,
    struct monad_event_descriptor const **event)
{
    *event =
        &iterator->desc_table[iterator->last_seqno & iterator->capacity_mask];
    uint64_t const seqno =
        atomic_load_explicit(&(*event)->seqno, memory_order_acquire);
    if (__builtin_expect(seqno == iterator->last_seqno + 1, 1)) {
        return MONAD_EVENT_READY;
    }
    return seqno < iterator->last_seqno ? MONAD_EVENT_NOT_READY
                                        : MONAD_EVENT_GAP;
}

inline bool monad_event_iterator_advance(struct monad_event_iterator *iterator)
{
    struct monad_event_descriptor const *const event =
        &iterator->desc_table[iterator->last_seqno & iterator->capacity_mask];
    uint64_t const seqno =
        atomic_load_explicit(&event->seqno, memory_order_acquire);
    if (__builtin_expect(seqno == iterator->last_seqno + 1, 1)) {
        ++iterator->last_seqno;
        return true;
    }
    return false;
}

inline void const *monad_event_payload_peek(
    struct monad_event_iterator const *iterator,
    struct monad_event_descriptor const *event,
    _Atomic(uint64_t) const **page_overwrite_seqno)
{
    struct monad_event_payload_page const *const page =
        iterator->payload_pages[event->payload_page];
    void const *const ptr = (uint8_t const *)page + event->offset;
    *page_overwrite_seqno = &page->overwrite_seqno;
    return ptr;
}

inline enum monad_event_poll_result monad_event_iterator_copy_next(
    struct monad_event_iterator *iterator,
    struct monad_event_descriptor *event_dst, void *payload_buf,
    size_t payload_buf_size)
{
    uint64_t seqno;
    size_t copy_size;

    struct monad_event_descriptor const *const event_src =
        &iterator->desc_table[iterator->last_seqno & iterator->capacity_mask];
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
    if (__builtin_expect(seqno == iterator->last_seqno + 1, 1)) {
        copy_size = payload_buf_size > event_dst->length ? event_dst->length
                                                         : payload_buf_size;
        if (__builtin_expect(
                monad_event_payload_memcpy(
                    iterator, event_dst, payload_buf, copy_size) == nullptr,
                0)) {
            return MONAD_EVENT_PAYLOAD_EXPIRED;
        }
        (void)monad_event_iterator_advance(iterator);
        return MONAD_EVENT_READY;
    }
    return seqno < iterator->last_seqno ? MONAD_EVENT_NOT_READY
                                        : MONAD_EVENT_GAP;
}

inline void *monad_event_payload_memcpy(
    struct monad_event_iterator const *iterator,
    struct monad_event_descriptor const *event, void *dst, size_t n)
{
    _Atomic(uint64_t) const *page_overwrite_seqno;
    void const *const src =
        monad_event_payload_peek(iterator, event, &page_overwrite_seqno);
    memcpy(dst, src, n);
    if (__builtin_expect(
            atomic_load_explicit(page_overwrite_seqno, memory_order_acquire) >
                atomic_load_explicit(&event->seqno, memory_order_acquire),
            0)) {
        // The shared memory page this payload lives in has been reused by
        // later events. We didn't copy this fast enough to be sure that all
        // `n` bytes are valid.
        return nullptr;
    }
    return dst;
}

inline uint64_t
monad_event_iterator_reset(struct monad_event_iterator *iterator)
{
    return iterator->last_seqno = monad_event_iterator_sync_wait(iterator);
}
