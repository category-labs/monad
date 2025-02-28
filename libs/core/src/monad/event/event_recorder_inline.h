/**
 * @file
 *
 * This file defines routines for the event recorder that must be inlined
 * for the sake of performance.
 */

#ifndef MONAD_EVENT_RECORDER_INTERNAL
    #error This file should only be included directly by event_recorder.h
#endif

#include <pthread.h>
#include <stdbit.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#include <sys/queue.h>
#include <sys/types.h>
#include <sys/uio.h>

#include <monad/core/bit_util.h>
#include <monad/core/likely.h>
#include <monad/event/event.h>
#include <monad/event/event_types.h>

// TODO(ken): supposed to come from mem/align.h but the PR hasn't landed yet
[[gnu::always_inline]] static inline size_t
monad_round_size_to_align(size_t size, size_t align)
{
    return bit_round_up(size, stdc_trailing_zeros(align));
}

// Recorder state that is shared across all event rings
struct monad_event_recorder_shared_state
{
    alignas(64) pthread_mutex_t mtx;
    TAILQ_HEAD(, monad_event_recorder) recorders;
    struct monad_event_recorder *primary_recorder;
    uint64_t block_flow_count;
    uint16_t block_flow_id;
};

extern struct monad_event_recorder_shared_state
    g_monad_event_recorder_shared_state;

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
//   - fills in the event descriptor fields that relate to the payload
//
// This returns a pointer to the allocated slot in the event ring
static inline struct monad_event_descriptor *_monad_event_ring_reserve(
    struct monad_event_recorder *recorder, size_t payload_size, uint64_t *seqno,
    void **dst)
{
    struct monad_event_descriptor *event;
    uint64_t buffer_window_start;
    uint64_t payload_begin;
    uint64_t payload_end;
    uint64_t const WINDOW_INCR = 1UL << 24;

    struct monad_event_ring *const event_ring = &recorder->event_ring;
    struct monad_event_ring_control *const rctl = recorder->control;
    bool const store_payload_inline = payload_size <= sizeof event->payload;
    size_t const alloc_size =
        store_payload_inline ? 0 : monad_round_size_to_align(payload_size, 8);
    uint64_t const last_seqno =
        __atomic_fetch_add(&rctl->last_seqno, 1, __ATOMIC_RELAXED);
    payload_begin = __atomic_fetch_add(
        &rctl->next_payload_byte, alloc_size, __ATOMIC_RELAXED);
    // We're going to start filling in the fields of `event`. Overwrite its
    // sequence number to zero, in case this slot is occupied by an older event
    // and that older event is currently being examined by a reading thread.
    // This ensures the reader can always detect that fields are invalidated.
    event = &event_ring->descriptors[last_seqno & recorder->capacity_mask];
    __atomic_store_n(&event->seqno, 0, __ATOMIC_RELEASE);
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
    *seqno = last_seqno + 1;
    event->length = (uint32_t)payload_size;
    event->inline_payload = store_payload_inline;
    if (event->inline_payload) {
        *dst = event->payload;
    }
    else {
        *dst = &event_ring
                    ->payload_buf[payload_begin & recorder->payload_buf_mask];
        event->payload_buf_offset = payload_begin;
    }
    return event;
}

inline void monad_event_record(
    struct monad_event_recorder *recorder, enum monad_event_type event_type,
    void const *payload, size_t payload_size)
{
    extern uint32_t monad_event_get_txn_id();
    struct monad_event_descriptor *event;
    uint64_t seqno;
    uint64_t event_epoch_nanos;
    void *dst;

    if (MONAD_UNLIKELY(
            recorder == nullptr ||
            !__atomic_load_n(&recorder->control->enabled, __ATOMIC_RELAXED))) {
        // This event ring isn't enabled
        return;
    }

    event_epoch_nanos = monad_event_get_epoch_nanos();

    // Reserve the resources to record the event, copy the event payload,
    // populate all event fields, and signal that we're done by the atomic
    // store of the sequence number
    event = _monad_event_ring_reserve(recorder, payload_size, &seqno, &dst);
    memcpy(dst, payload, payload_size);
    event->type = event_type;
    event->block_flow_id = g_monad_event_recorder_shared_state.block_flow_id;
    event->txn_id = monad_event_get_txn_id();
    event->epoch_nanos = event_epoch_nanos;
    __atomic_store_n(&event->seqno, seqno, __ATOMIC_RELEASE);
}

inline void monad_event_recordv(
    struct monad_event_recorder *recorder, enum monad_event_type event_type,
    struct iovec const *iov, size_t iovlen)
{
    extern uint32_t monad_event_get_txn_id();
    struct monad_event_descriptor *event;
    uint64_t seqno;
    uint64_t event_epoch_nanos;
    void *dst;
    size_t payload_size = 0;

    // Vectored "gather I/O" version of monad_event_record; the comments in
    // that function apply here also
    if (MONAD_UNLIKELY(
            recorder == nullptr ||
            !__atomic_load_n(&recorder->control->enabled, __ATOMIC_RELAXED))) {
        return;
    }

    event_epoch_nanos = monad_event_get_epoch_nanos();
    for (size_t i = 0; i < iovlen; ++i) {
        payload_size += iov[i].iov_len;
    }
    event = _monad_event_ring_reserve(recorder, payload_size, &seqno, &dst);
    for (size_t i = 0; i < iovlen; ++i) {
        dst = mempcpy(dst, iov[i].iov_base, iov[i].iov_len);
    }
    event->type = event_type;
    event->block_flow_id = g_monad_event_recorder_shared_state.block_flow_id;
    event->txn_id = monad_event_get_txn_id();
    event->epoch_nanos = event_epoch_nanos;
    __atomic_store_n(&event->seqno, seqno, __ATOMIC_RELEASE);
}

inline bool monad_event_recorder_set_enabled(
    struct monad_event_recorder *recorder, bool enabled)
{
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;
    if (MONAD_UNLIKELY(
            enabled && recorder != rss->primary_recorder &&
            (rss->primary_recorder == nullptr ||
             !__atomic_load_n(
                 &rss->primary_recorder->control->enabled,
                 __ATOMIC_RELAXED)))) {
        // Cannot enable recorder because primary event recorder isn't enabled
        return false;
    }
    __atomic_store_n(&recorder->control->enabled, enabled, __ATOMIC_RELAXED);
    return enabled;
}

inline uint16_t monad_event_next_block_flow_id(
    struct monad_event_block_exec_header **exec_header)
{
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;
    unsigned long block_count =
        __atomic_fetch_add(&rss->block_flow_count, 1, __ATOMIC_RELAXED) + 1;
    uint16_t block_id = block_count & 0xFFF;
    if (block_id == 0) {
        // 0 is not a valid block id; take another one
        block_count =
            __atomic_fetch_add(&rss->block_flow_count, 1, __ATOMIC_RELAXED) + 1;
        block_id = block_count & 0xFFF;
    }
    *exec_header = &rss->primary_recorder->event_ring.blocks[block_id];
    rss->block_flow_id = block_id;
    return block_id;
}

inline void monad_event_clear_block_flow_id()
{
    g_monad_event_recorder_shared_state.block_flow_id = 0;
}
