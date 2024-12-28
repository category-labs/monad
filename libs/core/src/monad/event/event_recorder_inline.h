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
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#include <sys/queue.h>

#include <monad/core/bit_util.h>
#include <monad/core/likely.h>
#include <monad/core/spinlock.h>
#include <monad/event/event.h>

struct monad_event_payload_page;
struct monad_event_recorder_thr;

// TODO(ken): supposed to come from mem/align.h but the PR hasn't landed yet
[[gnu::always_inline]] static inline size_t
monad_round_size_to_align(size_t size, size_t align)
{
    return bit_round_up(size, stdc_trailing_zeros(align));
}

// State of an event recorder; there is one of these for each event ring type.
// Each one owns an MPMC event fragment ring
struct monad_event_recorder
{
    alignas(64) atomic_bool enabled;
    enum monad_event_ring_type ring_type;
    struct monad_event_ring event_ring;
    int control_fd;
    int fragment_table_fd;
    alignas(64) atomic_bool initialized;
    monad_spinlock_t lock;
};

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

static inline struct monad_event_fragment *_monad_event_alloc_ring_fragments(
    struct monad_event_ring *event_ring, size_t payload_len, uint64_t *seqno,
    uint64_t *frag_count)
{
    __uint128_t desired;
    struct monad_event_ring_control *const ctrl = event_ring->control;
    *frag_count = payload_len / MONAD_EVENT_MAX_INLINE;
    if (*frag_count * MONAD_EVENT_MAX_INLINE != payload_len ||
        payload_len == 0) {
        ++*frag_count;
    }

    __uint128_t next =
        __atomic_load_n(&ctrl->seqno_fragment_next, __ATOMIC_RELAXED);
TryAgain:
    *seqno = (uint64_t)(next >> 64);
    uint64_t const fragment_start = (uint64_t)next;
    desired = (__uint128_t)(*seqno + 1) << 64 |
              (__uint128_t)(fragment_start + *frag_count);
    if (!__atomic_compare_exchange_n(
            &ctrl->seqno_fragment_next,
            &next,
            desired,
            true,
            __ATOMIC_ACQ_REL,
            __ATOMIC_ACQUIRE)) {
        goto TryAgain;
    }
    return &event_ring
                ->fragment_table[fragment_start & event_ring->capacity_mask];
}

inline void monad_event_record(
    struct monad_event_recorder *recorder, enum monad_event_type event_type,
    uint8_t flags, void const *payload, size_t payload_size)
{
    extern uint32_t monad_event_get_txn_num();
    struct monad_event_fragment *fragments;
    struct monad_event_recorder_thr *thread_cache;
    uint64_t seqno;
    uint64_t frag_count;
    uint64_t event_time;
    uint16_t copy_len;

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
    fragments = _monad_event_alloc_ring_fragments(
        &recorder->event_ring, payload_size, &seqno, &frag_count);

    // First fragment is special
    fragments[0].header.type = event_type;
    copy_len = fragments[0].header.inline_length =
        payload_size > MONAD_EVENT_MAX_INLINE ? MONAD_EVENT_MAX_INLINE
                                              : (uint16_t)payload_size;
    fragments[0].header.frag_no = 0;
    fragments[0].header.frag_count = (uint16_t)frag_count;
    fragments[0].header.pop_scope = flags & MONAD_EVENT_POP_SCOPE ? 1U : 0U;
    fragments[0].header.total_length = payload_size & 0x7FFFFFUL;
    fragments[0].header.source_id = thread_cache->source_id;
    fragments[0].header.block_flow_id =
        g_monad_event_recorder_shared_state.block_flow_id & 0xFFFU;
    fragments[0].header.txn_num = monad_event_get_txn_num() & 0xFFFFFU;
    fragments[0].header.epoch_nanos = event_time;
    memcpy(fragments[0].payload, payload, copy_len);
    payload = (uint8_t const *)payload + copy_len;
    payload_size -= copy_len;

    for (uint64_t f = 1; f < frag_count; ++f) {
        fragments[f].header.frag_no = (uint16_t)f;
        fragments[f].header.frag_count = (uint16_t)frag_count;
        copy_len = fragments[f].header.inline_length =
            payload_size > MONAD_EVENT_MAX_INLINE ? MONAD_EVENT_MAX_INLINE
                                                  : (uint16_t)payload_size;
        atomic_store_explicit(
            &fragments[f].header.seqno, seqno, memory_order_release);
        memcpy(fragments[f].payload, payload, copy_len);
        payload = (uint8_t const *)payload + copy_len;
        payload_size -= copy_len;
    }
    atomic_store_explicit(
        &fragments[0].header.seqno, seqno, memory_order_release);
}

static void _monad_event_inline_payload_memcpy(
    struct monad_event_fragment *fragment, size_t *payload_len,
    struct iovec **iov_p)
{
    struct iovec *iov = *iov_p;
    uint16_t copylen = fragment->header.inline_length =
        *payload_len > sizeof fragment->payload
            ? (uint16_t)(sizeof fragment->payload)
            : (uint16_t)*payload_len;
    uint16_t copied = 0;
    while (copied < copylen) {
        uint16_t resid = copylen - copied;
        if (iov->iov_len < resid) {
            memcpy(fragment->payload + copied, iov->iov_base, iov->iov_len);
            copied += (uint16_t)iov->iov_len;
            *iov_p = ++iov;
            continue;
        }
        memcpy(fragment->payload + copied, iov->iov_base, resid);
        copied += resid;
        iov->iov_base = (uint8_t *)iov->iov_base + resid;
        iov->iov_len -= resid;
        if (iov->iov_len == 0) {
            *iov_p = ++iov;
        }
    }
    *payload_len -= copylen;
}

inline void monad_event_recordv(
    struct monad_event_recorder *recorder, enum monad_event_type event_type,
    uint8_t flags, struct iovec *iov, size_t iovlen)
{
    extern uint32_t monad_event_get_txn_num();
    struct monad_event_fragment *fragments;
    struct monad_event_recorder_thr *thread_cache;
    uint64_t seqno;
    uint64_t frag_count;
    uint64_t event_time;
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
    fragments = _monad_event_alloc_ring_fragments(
        &recorder->event_ring, payload_size, &seqno, &frag_count);

    // First fragment is special
    fragments[0].header.type = event_type;
    fragments[0].header.frag_no = 0;
    fragments[0].header.frag_count = (uint16_t)frag_count;
    fragments[0].header.pop_scope = flags & MONAD_EVENT_POP_SCOPE ? 1U : 0U;
    fragments[0].header.total_length = payload_size & 0x7FFFFFUL;
    fragments[0].header.source_id = thread_cache->source_id;
    fragments[0].header.block_flow_id =
        g_monad_event_recorder_shared_state.block_flow_id & 0xFFFU;
    fragments[0].header.txn_num = monad_event_get_txn_num() & 0xFFFFFU;
    fragments[0].header.epoch_nanos = event_time;
    _monad_event_inline_payload_memcpy(&fragments[0], &payload_size, &iov);

    for (uint64_t f = 1; f < frag_count; ++f) {
        fragments[f].header.frag_no = (uint16_t)f;
        fragments[f].header.frag_count = (uint16_t)frag_count;
        atomic_store_explicit(
            &fragments[f].header.seqno, seqno, memory_order_release);
        _monad_event_inline_payload_memcpy(&fragments[f], &payload_size, &iov);
    }
    atomic_store_explicit(
        &fragments[0].header.seqno, seqno, memory_order_release);
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
