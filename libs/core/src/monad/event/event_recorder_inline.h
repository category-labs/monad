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

// Allocate event payload memory from a payload page, and fill in the event
// descriptor to refer to it
static void *_monad_event_alloc_payload(
    struct monad_event_recorder *, struct monad_event_recorder_thr *,
    size_t payload_size, uint16_t *page_id, uint32_t *offset,
    uint64_t *page_switched_time);

// Allocate memory from a payload page; used to directly allocate chunks from
// the metadata page
static void *_monad_event_alloc_from_fixed_page(
    struct monad_event_payload_page *, size_t payload_size, uint32_t *offset);

// When a payload page is full, the thread allocator calls this routine to
// return it to page pool and request a new page; see event_recorder.c
extern struct monad_event_payload_page *
_monad_event_recorder_switch_page(struct monad_event_payload_page *);

// Force the activation of a payload page; used the first time a thread
// records something
extern struct monad_event_payload_page *
_monad_event_activate_payload_page(struct monad_event_payload_page_pool *);

TAILQ_HEAD(monad_event_payload_page_queue, monad_event_payload_page);

// Event payloads live on slabs of memory called "payload pages". Each thread
// caches an active page per recorder in a thread_local so it can allocate
// without locking, and when it fills up a new page is taken from this pool
struct monad_event_payload_page_pool
{
    alignas(64) monad_spinlock_t lock;
    struct monad_event_payload_page_queue active_pages;
    struct monad_event_payload_page_queue free_pages;
    size_t active_page_count;
    size_t free_page_count;
    size_t pages_allocated;
    _Atomic(uint64_t) const *last_seqno;
};

// State of an event recorder; there is one of these for each event ring type.
// Each one owns an MPMC event descriptor ring and a payload page pool
struct monad_event_recorder
{
    alignas(64) atomic_bool enabled;
    enum monad_event_ring_type ring_type;
    struct monad_event_ring event_ring;
    struct monad_event_payload_page **all_pages;
    size_t all_pages_size;
    struct monad_event_payload_page_pool payload_page_pool;
    int control_fd;
    int descriptor_table_fd;
    alignas(64) atomic_bool initialized;
    monad_spinlock_t lock;
};

// Recorder state that is shared across all event rings
struct monad_event_recorder_shared_state
{
    alignas(64) monad_spinlock_t lock;
    uint64_t thread_source_ids;
    pthread_key_t thread_cache_key;
    TAILQ_HEAD(, monad_event_recorder_thr) thread_caches;
    struct monad_event_payload_page *metadata_page;
    struct monad_event_block_exec_header *block_header_table;
    struct monad_event_thread_info *thread_info_table;
    uint64_t process_id;
    atomic_ulong block_flow_count;
    uint16_t block_flow_id;
};

extern struct monad_event_recorder
    g_monad_event_recorders[MONAD_EVENT_RING_COUNT];

extern struct monad_event_recorder_shared_state
    g_monad_event_recorder_shared_state;

// To make recording as fast as possible, some of the recorder state is cached
// in this thread-local object; namely, each thread has its own active payload
// page that it can allocate event payloads from without locking the page pool
struct monad_event_recorder_thr
{
    uint8_t source_id;
    struct monad_event_payload_page *payload_page[MONAD_EVENT_RING_COUNT];
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

static inline struct monad_event_descriptor *
_monad_event_ring_reserve_descriptor(
    struct monad_event_ring *event_ring, uint64_t *seqno)
{
    struct monad_event_ring_control *const ctrl = event_ring->control;

    // Atomically increment the control page's `last_seqno` register. The
    // semantics of this value are:
    //
    //    1. When read, it will give the last sequence number that was
    //       allocated to an event.
    //
    //    2. When atomically incremented, the incrementor becomes the owner
    //       of the new "last sequence number", i.e., this is the sequence
    //       number implicitly given to the incrementor, to record its event.
    //
    // Because the sequence number is the same as the (unbounded) array index
    // plus 1, the predecessor value returned by atomic_fetch_add_explicit
    // is also the array index where the event descriptor will be stored
    // (modulo the ring size). Thus, reserving a sequence number for an event
    // also reserves an array slot in the ring buffer to hold the event
    // descriptor for that event.
    //
    // We return a pointer to that descriptor for the caller to manipulate.
    // When the caller is finished populating the descriptor fields details,
    // the caller is responsible for performing an atomic store of the sequence
    // number with memory_order_release semantics. That store acts as the
    // necessary barrier to ensure all other memory changes associated with
    // recording the event become visible in other threads.
    uint64_t const prev_seqno =
        atomic_fetch_add_explicit(&ctrl->last_seqno, 1, memory_order_relaxed);
    *seqno = prev_seqno + 1;
    struct monad_event_descriptor *event = &event_ring
                ->descriptor_table[prev_seqno & event_ring->capacity_mask];
    // We're going to start filling in the fields of `event`. Overwrite its
    // sequence number to zero, in case this slot is occupied by an older event
    // and is currently being examined by a reading thread. This will ensure
    // the reader can always detect that it has changed.
    atomic_store_explicit(&event->seqno, 0, memory_order_release);
    return event;
}

inline void *_monad_event_alloc_payload(
    struct monad_event_recorder *recorder,
    struct monad_event_recorder_thr *thread_cache, size_t payload_size,
    uint16_t *page_id, uint32_t *offset, uint64_t *event_time)
{
    extern uint32_t monad_event_get_txn_num();
    uint64_t switch_event_seqno;
    struct monad_event_descriptor *switch_event;
    struct monad_event_payload_page *page;
    size_t allocation_size;
    void *payload;

    page = thread_cache->payload_page[recorder->ring_type];
    if (MONAD_UNLIKELY(page == nullptr)) {
        // Rare corner case: the first time we're recording on a particular
        // thread, the thread-local active page will be missing. This could be
        // prevented by making sure it's always ready, but that is more complex
        // because the initialization would have to happen in two places
        // (depending on whether the thread cache was created before or after
        // the recorder was initialized).
        page = thread_cache->payload_page[recorder->ring_type] =
            _monad_event_activate_payload_page(&recorder->payload_page_pool);
    }

    // The allocation size is potentially larger than the payload size, so we
    // can guarantee alignment. We explicitly use pointer alignment here
    // because max_align_t is large enough on glibc x64 to be wasteful (32).
    allocation_size = monad_round_size_to_align(payload_size, sizeof(void *));
    if (MONAD_UNLIKELY(page->heap_next + allocation_size > page->heap_end)) {
        // Not enough memory left on this page; switch to a free page
        page = thread_cache->payload_page[recorder->ring_type] =
            _monad_event_recorder_switch_page(page);

        // Manually inject a page switch event descriptor into the new page.
        // We steal the original event's events' timestamp, then replace it
        // with a new timestamp.
        switch_event = _monad_event_ring_reserve_descriptor(
            &recorder->event_ring, &switch_event_seqno);
        switch_event->type = MONAD_EVENT_THR_PAGE_SWITCH;
        switch_event->payload_page = page->page_id;
        switch_event->offset = 0;
        switch_event->pop_scope = 0;
        switch_event->length = 0;
        switch_event->source_id = thread_cache->source_id;
        switch_event->block_flow_id =
            g_monad_event_recorder_shared_state.block_flow_id & 0xFFFU;
        switch_event->txn_num = monad_event_get_txn_num() & 0xFFFFFU;
        switch_event->epoch_nanos = *event_time;
        atomic_store_explicit(
            &switch_event->seqno, switch_event_seqno, memory_order_release);
        *event_time = monad_event_timestamp();
    }

    // Fill in the descriptor with the payload memory details
    *page_id = page->page_id;
    *offset = (uint32_t)(page->heap_next - (uint8_t *)page);

    // Set the payload pointer and mark the space as allocated in the event page
    payload = page->heap_next;
    page->heap_next += allocation_size;
    ++page->event_count;
    return payload;
}

inline void *_monad_event_alloc_from_fixed_page(
    struct monad_event_payload_page *page, size_t payload_size,
    uint32_t *offset)
{
    void *payload;

    if (MONAD_UNLIKELY(page->heap_next + payload_size > page->heap_end)) {
        // Not enough memory left on this page
        if (offset != nullptr) {
            *offset = 0;
        }
        return nullptr;
    }
    payload = page->heap_next;
    if (offset != nullptr) {
        *offset = (uint32_t)(page->heap_next - (uint8_t *)page);
    }
    page->heap_next += payload_size;
    ++page->event_count;
    return payload;
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
    uint16_t page_id;
    uint32_t page_offset;
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
    // Allocate the payload immediately, we do this first because calling
    // this function can switch the activate page, and that needs to have
    // an overwrite_seqno allocated before we allocate our sequence number.
    dst = _monad_event_alloc_payload(
        recorder,
        thread_cache,
        payload_size,
        &page_id,
        &page_offset,
        &event_time);
    event = _monad_event_ring_reserve_descriptor(&recorder->event_ring, &seqno);
    event->type = event_type;
    event->payload_page = page_id;
    event->offset = page_offset;
    event->pop_scope = flags & MONAD_EVENT_POP_SCOPE ? 1U : 0U;
    event->length = payload_size & 0x7FFFFFUL;
    event->source_id = thread_cache->source_id;
    event->block_flow_id =
        g_monad_event_recorder_shared_state.block_flow_id & 0xFFFU;
    event->txn_num = monad_event_get_txn_num() & 0xFFFFFU;
    event->epoch_nanos = event_time;
    memcpy(dst, payload, payload_size);
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
    uint16_t page_id;
    uint32_t page_offset;
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
    dst = _monad_event_alloc_payload(
        recorder,
        thread_cache,
        payload_size,
        &page_id,
        &page_offset,
        &event_time);
    for (size_t i = 0; i < iovlen; ++i) {
        dst = mempcpy(dst, iov[i].iov_base, iov[i].iov_len);
    }
    event = _monad_event_ring_reserve_descriptor(&recorder->event_ring, &seqno);
    event->type = event_type;
    event->payload_page = page_id;
    event->offset = page_offset;
    event->pop_scope = flags & MONAD_EVENT_POP_SCOPE ? 1U : 0U;
    event->length = payload_size & 0x7FFFFFUL;
    event->source_id = thread_cache->source_id;
    event->block_flow_id =
        g_monad_event_recorder_shared_state.block_flow_id & 0xFFFU;
    event->txn_num = monad_event_get_txn_num() & 0xFFFFFU;
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
    return &rss->block_header_table[block_id];
}

inline void monad_event_recorder_start_block(
    struct monad_event_block_exec_header const *block_exec_header)
{
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;
    rss->block_flow_id =
        (size_t)(block_exec_header - rss->block_header_table) & 0xFFFU;
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
