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

struct monad_event_thread_state;
struct monad_event_payload_page;

// TODO(ken): supposed to come from mem/align.h but the PR hasn't landed yet
[[gnu::always_inline]] static inline size_t
monad_round_size_to_align(size_t size, size_t align)
{
    return bit_round_up(size, stdc_trailing_zeros(align));
}

// Allocate event payload memory from a payload page, and fill in the event
// descriptor to refer to it
static void *_monad_event_alloc_payload(
    struct monad_event_recorder *, struct monad_event_thread_state *,
    struct monad_event_descriptor *, size_t payload_size);

// Allocate memory from a payload page; used to directly allocate chunks from
// the metadata page
static void *_monad_event_alloc_from_fixed_page(
    struct monad_event_payload_page *, size_t payload_size, uint32_t *offset);

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
    _Atomic(uint64_t) const *prod_next;
};

// State of an event recorder; there is one of these for each event queue type.
// Each one owns an MPMC event descriptor ring and a payload page pool
struct monad_event_recorder
{
    alignas(64) atomic_bool enabled;
    enum monad_event_queue_type queue_type;
    struct monad_event_ring event_ring;
    struct monad_event_payload_page **all_pages;
    size_t all_pages_size;
    struct monad_event_payload_page_pool payload_page_pool;
    alignas(64) atomic_bool initialized;
    monad_spinlock_t lock;
};

// Recorder state that is shared across all event queues
struct monad_event_recorder_shared_state
{
    alignas(64) monad_spinlock_t lock;
    uint64_t thread_source_ids;
    pthread_key_t thread_state_key;
    TAILQ_HEAD(, monad_event_thread_state) thread_states;
    struct monad_event_payload_page *metadata_page;
    struct monad_event_block_exec_header *block_header_table;
    struct monad_event_thread_info *thread_info_table;
    uint64_t process_id;
    atomic_ulong block_flow_count;
    uint16_t block_flow_id;
};

extern struct monad_event_recorder
    g_monad_event_recorders[MONAD_EVENT_QUEUE_COUNT];

extern struct monad_event_recorder_shared_state
    g_monad_event_recorder_shared_state;

// To make recording as fast as possible, some of the recorder state is cached
// in this thread-local object; namely, each thread has its own active payload
// page that it can allocate event payloads from without locking the page pool
struct monad_event_thread_state
{
    uint8_t source_id;
    struct monad_event_payload_page *payload_page[MONAD_EVENT_QUEUE_COUNT];
    uint64_t thread_id;
    TAILQ_ENTRY(monad_event_thread_state) next;
};

#ifdef __cplusplus
constinit
#endif
    extern thread_local struct monad_event_thread_state
        g_tls_monad_thread_state;

// Returns the thread record for the calling thread
static struct monad_event_thread_state *_monad_event_get_thread_state();

/*
 * Inline function definitions
 */

inline bool monad_event_recorder_set_enabled(
    enum monad_event_queue_type queue_type, bool enabled)
{
    struct monad_event_recorder *const recorder =
        &g_monad_event_recorders[queue_type];

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

inline struct monad_event_thread_state *_monad_event_get_thread_state()
{
    // Init routine called the first time the thread recorder is accessed;
    // see event_recorder.c
    extern void _monad_event_init_thread_state(
        struct monad_event_thread_state *);

    if (MONAD_UNLIKELY(g_tls_monad_thread_state.thread_id == 0)) {
        _monad_event_init_thread_state(&g_tls_monad_thread_state);
    }
    return &g_tls_monad_thread_state;
}

inline void *_monad_event_alloc_payload(
    struct monad_event_recorder *recorder,
    struct monad_event_thread_state *thread_state,
    struct monad_event_descriptor *event, size_t payload_size)
{
    struct monad_event_payload_page *page;
    size_t allocation_size;
    void *payload;

    // When a payload page is full, the thread allocator calls this routine to
    // return it to page pool and request a new page; see event_recorder.c
    extern struct monad_event_payload_page *_monad_event_recorder_switch_page(
        struct monad_event_payload_page *);

    page = thread_state->payload_page[recorder->queue_type];
    if (MONAD_UNLIKELY(page == nullptr)) {
        // Rare corner case: the first time we're recording on a particular
        // thread, the thread-local active page will be missing. This could be
        // prevented by making sure it's always ready, but that is more complex
        // because the initialization would have to happen in two places.
        extern struct monad_event_payload_page *_monad_event_alloc_payload_page(
            struct monad_event_payload_page_pool *);
        page = thread_state->payload_page[recorder->queue_type] =
            _monad_event_alloc_payload_page(&recorder->payload_page_pool);
    }

    // The allocation size is potentially larger than the payload size, so we
    // can guarantee alignment. We explicitly use pointer alignment here
    // because max_align_t is large enough on glibc x64 to be wasteful (32).
    allocation_size = monad_round_size_to_align(payload_size, sizeof(void *));
    if (MONAD_UNLIKELY(page->heap_next + allocation_size > page->heap_end)) {
        // Not enough memory left on this page; switch to a free page
        page = thread_state->payload_page[recorder->queue_type] =
            _monad_event_recorder_switch_page(page);
        // Manually inject a page allocation event descriptor into the new page
        monad_event_record(recorder, MONAD_EVENT_THR_PAGE_ALLOC, 0, nullptr, 0);
    }

    // Fill in the descriptor with the payload memory details
    event->payload_page = page->page_id;
    event->offset = (uint32_t)(page->heap_next - (uint8_t *)page);
    event->length = payload_size & 0x7FFFFFUL;
    event->source_id = thread_state->source_id;

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

static inline struct monad_event_descriptor *
_monad_event_alloc_queue_descriptor(
    struct monad_event_ring *event_ring, uint64_t *seqno)
{
    struct monad_event_ring_control *const ctrl = event_ring->control;

    // Claim ownership of the `prod_next` descriptor, which is both the write
    // index (after masking) and the new sequence number when 1 is added. We
    // return a pointer to this descriptor for the caller to manipulate. When
    // they are finished populating the descriptor fields details, the caller
    // is responsible for performing an atomic store of the sequence number
    // with memory_order_release semantics. This acts as the necessary barrier
    // to ensure all other changes to the descriptor become visible in other
    // threads.
    uint64_t const prod_next =
        atomic_fetch_add_explicit(&ctrl->prod_next, 1, memory_order_relaxed);
    *seqno = prod_next + 1;
    return &event_ring->descriptor_table[prod_next & event_ring->capacity_mask];
}

inline void monad_event_record(
    struct monad_event_recorder *recorder, enum monad_event_type event_type,
    uint8_t flags, void const *payload, size_t payload_size)
{
    extern uint32_t monad_event_get_txn_num();
    struct monad_event_descriptor *event;
    struct monad_event_thread_state *thread_state;
    uint64_t seqno;
    void *dst;

    if (MONAD_UNLIKELY(
            !atomic_load_explicit(&recorder->enabled, memory_order_acquire))) {
        // This recorder isn't enabled
        return;
    }

    // Get the thread state immediately, before taking the timestamp. Although
    // this distorts the timestamp a bit, it this prevents time appearing to go
    // backwards on the thread with respect to the THREAD_CREATE event, which
    // is emitted if this thread is recording for this first
    thread_state = _monad_event_get_thread_state();
    event = _monad_event_alloc_queue_descriptor(&recorder->event_ring, &seqno);
    event->epoch_nanos = monad_event_timestamp();
    event->type = event_type;
    event->pop_scope = flags & MONAD_EVENT_POP_SCOPE ? 1U : 0U;
    event->block_flow_id =
        g_monad_event_recorder_shared_state.block_flow_id & 0xFFFU;
    event->txn_num = monad_event_get_txn_num() & 0xFFFFFU;
    dst =
        _monad_event_alloc_payload(recorder, thread_state, event, payload_size);
    memcpy(dst, payload, payload_size);
    atomic_store_explicit(&event->seqno, seqno, memory_order_release);
}

inline void monad_event_recordv(
    struct monad_event_recorder *recorder, enum monad_event_type event_type,
    uint8_t flags, struct iovec const *iov, size_t iovlen)
{
    extern uint32_t monad_event_get_txn_num();
    struct monad_event_descriptor *event;
    struct monad_event_thread_state *thread_state;
    uint64_t seqno;
    void *dst;
    size_t payload_size = 0;

    if (MONAD_UNLIKELY(
            !atomic_load_explicit(&recorder->enabled, memory_order_acquire))) {
        // This recorder isn't enabled
        return;
    }

    thread_state = _monad_event_get_thread_state();
    event = _monad_event_alloc_queue_descriptor(&recorder->event_ring, &seqno);
    event->epoch_nanos = monad_event_timestamp();
    event->type = event_type;
    event->pop_scope = flags & MONAD_EVENT_POP_SCOPE ? 1U : 0U;
    event->block_flow_id =
        g_monad_event_recorder_shared_state.block_flow_id & 0xFFFU;
    event->txn_num = monad_event_get_txn_num() & 0xFFFFFU;
    for (size_t i = 0; i < iovlen; ++i) {
        payload_size += iov[i].iov_len;
    }
    dst =
        _monad_event_alloc_payload(recorder, thread_state, event, payload_size);
    for (size_t i = 0; i < iovlen; ++i) {
        dst = mempcpy(dst, iov[i].iov_base, iov[i].iov_len);
    }
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
