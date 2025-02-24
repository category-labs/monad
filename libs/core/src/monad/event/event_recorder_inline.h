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
#include <sys/uio.h>

#include <monad/core/bit_util.h>
#include <monad/core/likely.h>
#include <monad/event/event.h>
#include <monad/event/event_ring_db.h>

struct monad_event_recorder_thr;

// TODO(ken): supposed to come from mem/align.h but the PR hasn't landed yet
[[gnu::always_inline]] static inline size_t
monad_round_size_to_align(size_t size, size_t align)
{
    return bit_round_up(size, stdc_trailing_zeros(align));
}

// State of an event recorder; there is one of these for each event ring type.
// Owns the shared memory segments for the ring and the state change mutex
struct monad_event_recorder
{
    struct monad_event_ring_db_entry *db_entry;
    struct monad_event_ring event_ring;
    alignas(64) pthread_mutex_t config_mtx;
};

// Recorder state that is shared across all event rings
struct monad_event_recorder_shared_state
{
    alignas(64) pthread_mutex_t mtx;
    uint64_t thread_source_ids;
    pthread_key_t thread_cache_key;
    TAILQ_HEAD(, monad_event_recorder_thr) thread_caches;
    char *shm_name;
    struct monad_event_ring_db ring_db;
    uint64_t block_flow_count;
    uint16_t block_flow_id;
};

extern struct monad_event_recorder
    g_monad_event_recorders[MONAD_EVENT_RING_COUNT];

extern struct monad_event_recorder_shared_state
    g_monad_event_recorder_shared_state;

// To make recording as fast as possible, some of the recorder state is cached
// in this thread-local object
struct monad_event_recorder_thr
{
    uint8_t source_id;
    uint64_t thread_id;
    TAILQ_ENTRY(monad_event_recorder_thr) next;
};

#ifdef __cplusplus
constinit
#endif
    extern thread_local struct monad_event_recorder_thr
        g_tls_monad_recorder_thread_cache;

// Returns the recorder thread-local for the calling thread
static struct monad_event_recorder_thr *
_monad_event_recorder_get_thread_cache();

/*
 * Inline function definitions
 */

inline bool monad_event_recorder_set_enabled(
    enum monad_event_ring_type ring_type, bool enabled)
{
    enum monad_event_ring_state cur_ring_state;
    enum monad_event_ring_state next_ring_state;
    struct monad_event_recorder *const recorder =
        &g_monad_event_recorders[ring_type];

    if (MONAD_UNLIKELY(recorder->db_entry == nullptr)) {
        // Global event system init hasn't happened yet; can't be enabled
        return false;
    }

    cur_ring_state = __atomic_load_n(
        &recorder->db_entry->ring_control.ring_state, __ATOMIC_RELAXED);
TryAgain:
    if (MONAD_UNLIKELY(cur_ring_state == MONAD_EVENT_RING_OFFLINE)) {
        // Offline rings have no memory allocated for them; can't be enabled
        return false;
    }
    next_ring_state =
        enabled ? MONAD_EVENT_RING_ENABLED : MONAD_EVENT_RING_CONFIGURED;
    if (!__atomic_compare_exchange_n(
            &recorder->db_entry->ring_control.ring_state,
            &cur_ring_state,
            next_ring_state,
            false,
            __ATOMIC_RELAXED,
            __ATOMIC_RELAXED)) {
        // State change race; check that the ring wasn't placed offline and try
        // again
        goto TryAgain;
    }
    return enabled;
}

inline uint64_t monad_event_get_epoch_nanos()
{
    struct timespec now;
    (void)clock_gettime(CLOCK_REALTIME, &now);
    return (uint64_t)(now.tv_sec * 1'000'000'000L + now.tv_nsec);
}

inline struct monad_event_recorder_thr *_monad_event_recorder_get_thread_cache()
{
    // Init routine called the first time the thread recorder is accessed;
    // see event_recorder.c
    extern void _monad_event_recorder_init_thread_cache(
        struct monad_event_recorder_thr *);

    if (MONAD_UNLIKELY(g_tls_monad_recorder_thread_cache.thread_id == 0)) {
        _monad_event_recorder_init_thread_cache(
            &g_tls_monad_recorder_thread_cache);
    }
    return &g_tls_monad_recorder_thread_cache;
}

// Reserve the shared memory resources needed to record the next event; this
// does the following:
//
//   - allocates a sequence number for the event; this also reserves a slot in
//     the descriptor array for event's descriptor, since the array index and
//     sequence number are related by `array_index = (seqno - 1) % capacity`
//
//   - allocates space in the payload buffer for the event payload
//
//   - fills in the event descriptor fields that relate to the payload
static inline struct monad_event_descriptor *_monad_event_ring_reserve(
    struct monad_event_ring *event_ring, size_t payload_size, uint64_t *seqno,
    void **dst)
{
    struct monad_event_descriptor *event;
    uint64_t buffer_window_start;
    uint64_t payload_begin;
    uint64_t payload_end;
    uint64_t const WINDOW_INCR = MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE;
    struct monad_event_ring_control *const ctrl = event_ring->control;
    size_t const alloc_size =
        payload_size > 32 ? monad_round_size_to_align(payload_size, 8) : 0;
    uint64_t const last_seqno =
        __atomic_fetch_add(&ctrl->last_seqno, 1, __ATOMIC_RELAXED);
    payload_begin = __atomic_fetch_add(
        &ctrl->next_payload_byte, alloc_size, __ATOMIC_RELAXED);
    // We're going to start filling in the fields of `event`. Overwrite its
    // sequence number to zero, in case this slot is occupied by an older event
    // and that older event is currently being examined by a reading thread.
    // This ensures the reader can always detect that fields are invalidated.
    event = &event_ring->descriptors[last_seqno & (event_ring->capacity - 1)];
    __atomic_store_n(&event->seqno, 0, __ATOMIC_RELEASE);
    payload_end = payload_begin + alloc_size;
    buffer_window_start = __atomic_load_n(
        &event_ring->control->buffer_window_start, __ATOMIC_RELAXED);
    if (MONAD_UNLIKELY(
            payload_end - buffer_window_start >
            event_ring->payload_buf_size - WINDOW_INCR)) {
        // Slide the buffer window over by `WINDOW_INCR`, see the
        // "Sliding buffer window" section in `event_recorder.md`
        __atomic_compare_exchange_n(
            &event_ring->control->buffer_window_start,
            &buffer_window_start,
            buffer_window_start + WINDOW_INCR,
            false,
            __ATOMIC_RELAXED,
            __ATOMIC_RELAXED);
    }
    *seqno = last_seqno + 1;
    event->length = (uint32_t)payload_size;
    event->inline_payload = payload_size <= sizeof event->payload;
    if (event->inline_payload) {
        *dst = event->payload;
    }
    else {
        *dst = &event_ring->payload_buf
                    [payload_begin & (event_ring->payload_buf_size - 1)];
        event->payload_buf_offset = payload_begin;
    }
    return event;
}

inline void monad_event_record(
    struct monad_event_recorder *recorder, enum monad_event_type event_type,
    uint8_t flags, void const *payload, size_t payload_size)
{
    extern uint32_t monad_event_get_txn_id();
    struct monad_event_descriptor *event;
    struct monad_event_recorder_thr *thread_cache;
    uint64_t seqno;
    uint64_t event_epoch_nanos;
    void *dst;

    if (MONAD_UNLIKELY(
            __atomic_load_n(
                &recorder->event_ring.control->ring_state, __ATOMIC_ACQUIRE) !=
            MONAD_EVENT_RING_ENABLED)) {
        // This event ring isn't enabled
        return;
    }

    // Get the thread cache immediately, before taking the timestamp. Although
    // this distorts the timestamp a bit, this prevents time appearing to go
    // backwards on the thread with respect to the THREAD_CREATE event, which
    // is emitted when this thread is recording its first event
    thread_cache = _monad_event_recorder_get_thread_cache();
    event_epoch_nanos = monad_event_get_epoch_nanos();

    // Reserve the resources to record the event, then populate all event fields
    event = _monad_event_ring_reserve(
        &recorder->event_ring, payload_size, &seqno, &dst);
    memcpy(dst, payload, payload_size);
    event->type = event_type;
    event->block_flow_id = g_monad_event_recorder_shared_state.block_flow_id;
    event->source_id = thread_cache->source_id;
    event->pop_scope = flags & MONAD_EVENT_POP_SCOPE;
    event->txn_id = monad_event_get_txn_id();
    event->epoch_nanos = event_epoch_nanos;
    __atomic_store_n(&event->seqno, seqno, __ATOMIC_RELEASE);
}

inline void monad_event_recordv(
    struct monad_event_recorder *recorder, enum monad_event_type event_type,
    uint8_t flags, struct iovec const *iov, size_t iovlen)
{
    extern uint32_t monad_event_get_txn_id();
    struct monad_event_descriptor *event;
    struct monad_event_recorder_thr *thread_cache;
    uint64_t seqno;
    uint64_t event_epoch_nanos;
    void *dst;
    size_t payload_size = 0;

    // Vectored "gather I/O" version of monad_event_record; see the comments
    // in that function
    if (MONAD_UNLIKELY(
            __atomic_load_n(
                &recorder->event_ring.control->ring_state, __ATOMIC_ACQUIRE) !=
            MONAD_EVENT_RING_ENABLED)) {
        return;
    }

    thread_cache = _monad_event_recorder_get_thread_cache();
    event_epoch_nanos = monad_event_get_epoch_nanos();

    for (size_t i = 0; i < iovlen; ++i) {
        payload_size += iov[i].iov_len;
    }
    event = _monad_event_ring_reserve(
        &recorder->event_ring, payload_size, &seqno, &dst);
    for (size_t i = 0; i < iovlen; ++i) {
        dst = mempcpy(dst, iov[i].iov_base, iov[i].iov_len);
    }
    event->type = event_type;
    event->block_flow_id = g_monad_event_recorder_shared_state.block_flow_id;
    event->source_id = thread_cache->source_id;
    event->pop_scope = flags & MONAD_EVENT_POP_SCOPE;
    event->txn_id = monad_event_get_txn_id();
    event->epoch_nanos = event_epoch_nanos;
    __atomic_store_n(&event->seqno, seqno, __ATOMIC_RELEASE);
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
    *exec_header = &rss->ring_db.db_data->block_headers[block_id];
    rss->block_flow_id = block_id;
    return block_id;
}

inline void monad_event_clear_block_flow_id()
{
    g_monad_event_recorder_shared_state.block_flow_id = 0;
}
