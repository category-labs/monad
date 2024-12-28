/**
 * @file
 *
 * This file contains the implementation of the event iterator API, which is
 * entirely inlined for performance reasons.
 */

#ifndef MONAD_EVENT_ITERATOR_INTERNAL
    #error This file should only be included directly by event_iterator.h
#endif

#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include <monad/event/event.h>

static inline struct monad_event_fragment const *
monad_event_iterator_at(struct monad_event_iterator const *iter, uint64_t f)
{
    return &iter->fragment_table[f & iter->capacity_mask];
}

static inline enum monad_event_poll_result monad_event_iterator_peek_resume(
    struct monad_event_iterator *iter,
    struct monad_event_fragment const **begin,
    struct monad_event_fragment const **end)
{
    // Invariant: reassembly has started; iterator->next_index might be the
    // last fragment; we only advance if we _don't_ find the last fragment
    while (true) {
        struct monad_event_fragment const *next =
            monad_event_iterator_at(iter, iter->next_fragment);
        uint64_t const next_seqno =
            atomic_load_explicit(&next->header.seqno, memory_order_acquire);
        if (__builtin_expect(next_seqno > iter->scan_seqno, 0)) {
            return MONAD_EVENT_GAP;
        }
        if (__builtin_expect(next_seqno < iter->scan_seqno, 0)) {
            return MONAD_EVENT_PARTIAL;
        }
        if (next->header.frag_no + 1 == next->header.frag_count) {
            *end = ++next;
            if (iter->scan_seqno ==
                atomic_load_explicit(
                    &(*begin)->header.seqno, memory_order_acquire)) {
                return MONAD_EVENT_READY;
            }
            return MONAD_EVENT_GAP;
        }
        ++iter->next_fragment;
    }
}

static inline enum monad_event_poll_result monad_event_iterator_peek_start(
    struct monad_event_iterator *iter,
    struct monad_event_fragment const **begin,
    struct monad_event_fragment const **end)
{
    // Invariant: we're at the start of an event
    struct monad_event_fragment const *next =
        monad_event_iterator_at(iter, iter->next_fragment);
    uint64_t const next_seqno =
        atomic_load_explicit(&next->header.seqno, memory_order_acquire);
    if (__builtin_expect(next_seqno < iter->last_seqno, 0)) {
        return MONAD_EVENT_NOT_READY;
    }
    if (__builtin_expect(next_seqno == iter->last_seqno + 1, 1)) {
        *begin = next;
        iter->scan_seqno = next_seqno;
        if (next->header.frag_no + 1 == next->header.frag_count) {
            *end = ++next;
            return MONAD_EVENT_READY;
        }
        iter->begin = next;
        ++iter->next_fragment;
        return monad_event_iterator_peek_resume(iter, begin, end);
    }
    return MONAD_EVENT_GAP;
}

inline enum monad_event_poll_result monad_event_iterator_peek(
    struct monad_event_iterator *iter,
    struct monad_event_fragment const **begin,
    struct monad_event_fragment const **end)
{
    return iter->begin ? monad_event_iterator_peek_resume(iter, begin, end)
                       : monad_event_iterator_peek_start(iter, begin, end);
}

inline bool monad_event_iterator_advance(
    struct monad_event_iterator *iter, struct monad_event_fragment const *begin)
{
    if (atomic_load_explicit(&begin->header.seqno, memory_order_acquire) !=
        iter->scan_seqno) {
        return false;
    }
    ++iter->next_fragment;
    iter->last_seqno = iter->scan_seqno;
    iter->scan_seqno = 0;
    iter->begin = nullptr;
    return true;
}

inline enum monad_event_poll_result monad_event_iterator_copy_next(
    struct monad_event_iterator *iter, struct monad_event_header *header,
    void *payload_buf, size_t payload_buf_size)
{
    struct monad_event_fragment const *begin, *end;
    enum monad_event_poll_result pr =
        monad_event_iterator_peek(iter, &begin, &end);

    if (pr != MONAD_EVENT_READY) {
        return pr;
    }
#if defined(__cplusplus) && !defined(__clang__)
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Wclass-memaccess"
#endif
    memcpy(header, &begin->header, sizeof *header);
#if defined(__cplusplus) && !defined(__clang__)
    #pragma GCC diagnostic pop
#endif
    for (struct monad_event_fragment const *next = begin; next != end; ++next) {
        if (atomic_load_explicit(&next->header.seqno, memory_order_acquire) !=
            iter->scan_seqno) {
            return MONAD_EVENT_GAP;
        }
        size_t const copy_len = next->header.inline_length < payload_buf_size
                                    ? next->header.inline_length
                                    : payload_buf_size;
        payload_buf = mempcpy(payload_buf, next->payload, copy_len);
        payload_buf_size -= copy_len;
    }
    return monad_event_iterator_advance(iter, begin) ? MONAD_EVENT_READY
                                                     : MONAD_EVENT_GAP;
}

inline uint64_t monad_event_iterator_reset(struct monad_event_iterator *iter)
{
    struct monad_event_fragment const *frag;
    uint64_t most_recent_seqno;
    __uint128_t const next =
        __atomic_load_n(iter->seqno_fragment_next, __ATOMIC_ACQUIRE);
    uint64_t const next_seqno = (uint64_t)(next >> 64);
    uint64_t const next_fragment = (uint64_t)next;
    if (next_fragment == 0) {
        iter->last_seqno = 0;
        iter->next_fragment = 0;
    }
    frag = monad_event_iterator_at(iter, next_fragment - 1);
    do {
        most_recent_seqno =
            atomic_load_explicit(&frag->header.seqno, memory_order_acquire);
    }
    while (most_recent_seqno + 1 != next_seqno);
    iter->last_seqno = most_recent_seqno - 1;
    iter->next_fragment = next_fragment - frag->header.frag_count;
    return iter->last_seqno;
}
