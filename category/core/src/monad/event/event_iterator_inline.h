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

#ifdef __cplusplus
extern "C"
{
#endif

static inline uint64_t
monad_event_iterator_sync_wait(struct monad_event_iterator *iter)
{
    uint64_t const MAX_SYNC_SPIN = 100;
    uint64_t write_last_seqno =
        __atomic_load_n(&iter->control->last_seqno, __ATOMIC_ACQUIRE);
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
        size_t const index = (write_last_seqno - 1) & iter->desc_capacity_mask;
        struct monad_event_descriptor const *event = &iter->descriptors[index];
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

inline uint64_t monad_event_iterator_reset(struct monad_event_iterator *iter)
{
    return iter->read_last_seqno = monad_event_iterator_sync_wait(iter);
}

#ifdef __cplusplus
} // extern "C"
#endif
