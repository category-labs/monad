/**
 * @file
 *
 * This file contains the implementation of the event iterator API, which is
 * entirely inlined for performance reasons.
 */

#ifndef MONAD_EVENT_ITERATOR_INTERNAL
    #error This file should only be included directly by event_iterator.h
#endif

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include <monad/event/event.h>

static size_t _monad_event_round_size_to_align(size_t size, size_t align)
{
    return (size + (align - 1)) & ~(align - 1);
}

static inline struct monad_event_header const *
_monad_event_iterator_get_header(struct monad_event_iterator *iter)
{
    size_t const size_mask = iter->fifo_size - 1;
    uint8_t const *next_event_start =
        (uint8_t const *)iter->fifo_buf + (iter->read_position & size_mask);
    return (struct monad_event_header const *)next_event_start;
}

inline enum monad_event_poll_result monad_event_iterator_peek(
    struct monad_event_iterator *iter, struct monad_event_header *header,
    void const **payload)
{
    struct monad_event_range last_event_range;
    struct monad_event_header const *const ring_header =
        _monad_event_iterator_get_header(iter);
    __atomic_load(
        iter->ring_last_event_range, &last_event_range, __ATOMIC_ACQUIRE);
    if (last_event_range.end_byte - iter->read_position < sizeof *header) {
        // No event header materialized yet
        return MONAD_EVENT_NOT_READY;
    }
    *header = *ring_header;
    if (__builtin_expect(
            __atomic_load_n(iter->ring_next_byte, __ATOMIC_ACQUIRE) -
                    iter->read_position >=
                iter->fifo_size,
            0)) {
        // We cannot trust the contents of *header now
        return MONAD_EVENT_GAP;
    }
    *payload = ring_header + 1;
    return MONAD_EVENT_READY;
}

inline bool monad_event_iterator_advance(struct monad_event_iterator *iter)
{
    struct monad_event_header const *const ring_header =
        _monad_event_iterator_get_header(iter);
    uint32_t const length = ring_header->length;
    size_t const next_byte =
        __atomic_load_n(iter->ring_next_byte, __ATOMIC_ACQUIRE);
    if (__builtin_expect(
            next_byte - iter->read_position >= iter->fifo_size, 0)) {
        return false;
    }
    iter->read_position +=
        sizeof *ring_header + _monad_event_round_size_to_align(length, 8);
    return true;
}

inline enum monad_event_poll_result monad_event_iterator_copy_next(
    struct monad_event_iterator *iter, struct monad_event_header *header,
    void *payload_buf, size_t payload_buf_size)
{
    void const *ring_payload;
    enum monad_event_poll_result const pr =
        monad_event_iterator_peek(iter, header, &ring_payload);
    if (pr != MONAD_EVENT_READY) {
        return pr;
    }
    memcpy(
        payload_buf,
        ring_payload,
        payload_buf_size < header->length ? payload_buf_size : header->length);
    return monad_event_iterator_advance(iter) ? MONAD_EVENT_READY
                                              : MONAD_EVENT_GAP;
}

inline void monad_event_iterator_reset(struct monad_event_iterator *iter)
{
    struct monad_event_range er;
    __atomic_load(iter->ring_last_event_range, &er, __ATOMIC_ACQUIRE);
    iter->read_position = er.begin_byte;
}
