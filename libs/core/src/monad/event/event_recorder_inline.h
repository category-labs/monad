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
#include <stdatomic.h>
#include <stdbit.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#include <sys/queue.h>

#include <monad/core/bit_util.h>
#include <monad/core/likely.h>
#include <monad/event/event.h>

struct monad_event_recorder_thr;

// TODO(ken): supposed to come from mem/align.h but the PR hasn't landed yet
[[gnu::always_inline]] static inline size_t
monad_round_size_to_align(size_t size, size_t align)
{
    return bit_round_up(size, stdc_trailing_zeros(align));
}

// memfd_create(2) file descriptors for the shared memory segments of the
// `struct monad_event_ring`
struct monad_event_ring_fds
{
    int control_fd;
    int descriptor_array_fd;
    int payload_buf_fd;
};

// State of an event recorder; there is one of these for each event ring type.
// Owns the shared memory segments for the ring, and enabled/disable state
struct monad_event_recorder
{
    alignas(64) atomic_bool enabled;
    enum monad_event_ring_type ring_type;
    struct monad_event_ring event_ring;
    struct monad_event_ring_fds event_ring_fds;
    alignas(64) atomic_bool initialized;
    pthread_mutex_t init_mtx;
};

// Certain metadata event payloads are also stored in fixed-sized arrays, so
// that can be referenced out-of-band (see event.md for details). This object
// describes the metadata shared memory region and the base addresses of the
// metadata arrays
struct monad_event_metadata_page
{
    void *base_addr;
    size_t map_len;
    struct monad_event_block_exec_header *block_header_table;
    struct monad_event_thread_info *thread_info_table;
    int memfd;
    uint8_t *heap_begin;
    uint8_t *heap_next;
    uint8_t *heap_end;
};

// Recorder state that is shared across all event rings
struct monad_event_recorder_shared_state
{
    alignas(64) pthread_mutex_t mtx;
    uint64_t thread_source_ids;
    pthread_key_t thread_cache_key;
    TAILQ_HEAD(, monad_event_recorder_thr) thread_caches;
    struct monad_event_metadata_page metadata_page;
    uint64_t process_id;
    atomic_ulong block_flow_count;
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
    struct monad_event_recorder *const recorder =
        &g_monad_event_recorders[ring_type];

    // The common case, which must be fast: we're enabling/disabling after
    // all initialization has been performed
    if (MONAD_LIKELY(atomic_load_explicit(
            &recorder->initialized, memory_order_relaxed))) {
        return atomic_exchange_explicit(
            &recorder->enabled, enabled, memory_order_acq_rel);
    }
    // The slow, rare case: the recorder is not explicitly initialized, so
    // enabling will also trigger initialization with the default parameters;
    // see event_recorder.c
    extern bool _monad_event_recorder_set_enabled_slow(
        struct monad_event_recorder *, bool);
    return _monad_event_recorder_set_enabled_slow(recorder, enabled);
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
            !atomic_load_explicit(&recorder->enabled, memory_order_acquire))) {
        // This recorder isn't enabled
        return;
    }

    // Get the thread cache immediately, before taking the timestamp. Although
    // this distorts the timestamp a bit, this prevents time appearing to go
    // backwards on the thread with respect to the THREAD_CREATE event, which
    // is emitted when this thread is recording its first event
    thread_cache = _monad_event_recorder_get_thread_cache();
    event_epoch_nanos = monad_event_get_epoch_nanos();
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
            !atomic_load_explicit(&recorder->enabled, memory_order_acquire))) {
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
