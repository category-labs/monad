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
#include <monad/core/spinlock.h>
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
    int descriptor_table_fd;
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
    monad_spinlock_t lock;
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
    alignas(64) monad_spinlock_t lock;
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

inline uint64_t monad_event_timestamp()
{
#if MONAD_EVENT_USE_RDTSC
    #error cannot enable this yet; missing TSC HZ to ns mapping logic (use sysfs driver)
    // return __builtin_ia32_rdtsc();
#else
    return monad_event_get_epoch_nanos();
#endif
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

// In gcc (as of v14), __atomic_compare_exchange on a 16 byte value emits a
// call to libatomic rather than emitting a CMPXCHG16B instruction. The reason
// why is explained in gcc PR80878 and PR104688. To guarantee we have lock free
// atomics, we define a helper function `_monad_event_xchg_wr_state` which
// is __atomic_compare_exchange in clang and uses inline assembly in gcc.

#if defined(__GNUC__) && !defined(__clang__)

static inline bool _monad_event_xchg_wr_state(
    struct monad_event_ring_writer_state *wr_state,
    struct monad_event_ring_writer_state *expected,
    struct monad_event_ring_writer_state *desired)
{
    bool result;

    __asm__ __volatile__("lock; cmpxchg16b %1; setz %0"
                         : "=q"(result),
                           "+m"(*wr_state),
                           "+a"(expected->last_seqno),
                           "+d"(expected->next_payload_byte)
                         : "b"(desired->last_seqno),
                           "c"(desired->next_payload_byte)
                         : "cc");

    return result;
}

#else

static_assert(__atomic_always_lock_free(
    sizeof(struct monad_event_ring_writer_state), nullptr));

static inline bool _monad_event_xchg_wr_state(
    struct monad_event_ring_writer_state *wr_state,
    struct monad_event_ring_writer_state *expected,
    struct monad_event_ring_writer_state *desired)
{
    return __atomic_compare_exchange(
        wr_state, expected, desired, true, __ATOMIC_RELAXED, __ATOMIC_RELAXED);
}

#endif

// Reserve a slot in the descriptor table to hold a new event; this allocates
// a sequence number for the event and space in the payload buffer for its
// payload
static inline struct monad_event_descriptor *_monad_event_ring_reserve(
    struct monad_event_ring *event_ring, size_t payload_size, uint64_t *seqno,
    void **dst)
{
    struct monad_event_ring_writer_state cur_state;
    struct monad_event_ring_writer_state next_state;
    struct monad_event_descriptor *event;
    uint64_t buffer_window_start;
    uint64_t payload_end;
    uint64_t const WINDOW_INCR = MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE;
    struct monad_event_ring_control *const ctrl = event_ring->control;
    size_t const alloc_size =
        payload_size > 32 ? monad_round_size_to_align(payload_size, 8) : 0;
    // TODO(ken): this should be an __atomic_load of the entire structure, but
    //    splitting it apart makes it easier to deal with the missing 128-bit
    //    atomic loads in gcc
    cur_state.last_seqno =
        __atomic_load_n(&ctrl->wr_state.last_seqno, __ATOMIC_RELAXED);
    cur_state.next_payload_byte =
        __atomic_load_n(&ctrl->wr_state.next_payload_byte, __ATOMIC_RELAXED);
TryAgain:
    next_state.last_seqno = cur_state.last_seqno + 1;
    next_state.next_payload_byte = cur_state.next_payload_byte + alloc_size;
    while (
        !_monad_event_xchg_wr_state(&ctrl->wr_state, &cur_state, &next_state)) {
        goto TryAgain;
    }
    // We're going to start filling in the fields of `event`. Overwrite its
    // sequence number to zero, in case this slot is occupied by an older event
    // and that older event is currently being examined by a reading thread.
    // This ensures the reader can always detect that fields are invalidated.
    event = &event_ring->descriptor_table
                 [cur_state.last_seqno & (event_ring->capacity - 1)];
    atomic_store_explicit(&event->seqno, 0, memory_order_release);
    payload_end = cur_state.next_payload_byte;
    buffer_window_start = __atomic_load_n(
        &event_ring->control->buffer_window_start, __ATOMIC_RELAXED);
    if (MONAD_UNLIKELY(
            payload_end - buffer_window_start >
            event_ring->payload_buf_size - WINDOW_INCR)) {
        __atomic_compare_exchange_n(
            &event_ring->control->buffer_window_start,
            &buffer_window_start,
            buffer_window_start + WINDOW_INCR,
            false,
            __ATOMIC_RELAXED,
            __ATOMIC_RELAXED);
    }
    *seqno = next_state.last_seqno;
    event->length = (uint32_t)payload_size;
    event->inline_payload = payload_size <= sizeof event->payload;
    if (event->inline_payload) {
        *dst = event->payload;
    }
    else {
        *dst = &event_ring->payload_buf
                    [cur_state.next_payload_byte &
                     (event_ring->payload_buf_size - 1)];
        event->payload_buf_offset = cur_state.next_payload_byte;
    }
    return event;
}

inline void monad_event_record(
    struct monad_event_recorder *recorder, enum monad_event_type event_type,
    uint8_t flags, void const *payload, size_t payload_size)
{
    extern uint32_t monad_event_get_txn_num();
    struct monad_event_descriptor *event;
    struct monad_event_recorder_thr *thread_cache;
    uint64_t seqno;
    uint64_t event_time;
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
    event_time = monad_event_timestamp();
    event = _monad_event_ring_reserve(
        &recorder->event_ring, payload_size, &seqno, &dst);
    memcpy(dst, payload, payload_size);
    event->type = event_type;
    event->block_flow_id = g_monad_event_recorder_shared_state.block_flow_id;
    event->source_id = thread_cache->source_id;
    event->pop_scope = flags & MONAD_EVENT_POP_SCOPE;
    event->txn_num = monad_event_get_txn_num();
    event->epoch_nanos = event_time;
    atomic_store_explicit(&event->seqno, seqno, memory_order_release);
}

inline void monad_event_recordv(
    struct monad_event_recorder *recorder, enum monad_event_type event_type,
    uint8_t flags, struct iovec const *iov, size_t iovlen)
{
    extern uint32_t monad_event_get_txn_num();
    struct monad_event_descriptor *event;
    struct monad_event_recorder_thr *thread_cache;
    uint64_t seqno;
    uint64_t event_time;
    void *dst;
    size_t payload_size = 0;

    // Vectored "gather I/O" version of monad_event_record; see the comments
    // in that function
    if (MONAD_UNLIKELY(
            !atomic_load_explicit(&recorder->enabled, memory_order_acquire))) {
        return;
    }

    thread_cache = _monad_event_recorder_get_thread_cache();
    event_time = monad_event_timestamp();
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
    event->txn_num = monad_event_get_txn_num();
    event->epoch_nanos = event_time;
    atomic_store_explicit(&event->seqno, seqno, memory_order_release);
}

inline struct monad_event_block_exec_header *
monad_event_recorder_alloc_block_exec_header()
{
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;
    unsigned long block_count =
        atomic_fetch_add_explicit(
            &rss->block_flow_count, 1, memory_order_relaxed) +
        1;
    uint16_t block_id = block_count & 0xFFF;
    if (block_id == 0) {
        // 0 is not a valid block id; take another one
        block_count = atomic_fetch_add_explicit(
                          &rss->block_flow_count, 1, memory_order_relaxed) +
                      1;
        block_id = block_count & 0xFFF;
    }
    return &rss->metadata_page.block_header_table[block_id];
}

inline void monad_event_recorder_start_block(
    struct monad_event_block_exec_header const *block_exec_header)
{
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;
    rss->block_flow_id =
        (size_t)(block_exec_header - rss->metadata_page.block_header_table) &
        0xFFFU;
    MONAD_EVENT_MEMCPY(
        MONAD_EVENT_BLOCK_START,
        0,
        block_exec_header,
        sizeof *block_exec_header);
}

inline void monad_event_recorder_end_block(
    struct monad_event_block_exec_result const *block_exec_result)
{
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;
    MONAD_EVENT_MEMCPY(
        MONAD_EVENT_BLOCK_END,
        MONAD_EVENT_POP_SCOPE,
        block_exec_result,
        sizeof *block_exec_result);
    // TODO(ken): this is only for the moment, before Kevin's stuff lands
    MONAD_EVENT(MONAD_EVENT_BLOCK_FINALIZE, 0);
    rss->block_flow_id = 0;
}
