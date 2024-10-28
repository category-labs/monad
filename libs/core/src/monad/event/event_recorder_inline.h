/**
 * @file
 *
 * This file defines routines for the event recorder that must be inlined
 * for the sake of performance. The internals of the recorder are also
 * known to the event session and event server objects for the same reason.
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

#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/core/spinlock.h>
#include <monad/core/spinloop.h>
#include <monad/event/event.h>
#include <monad/event/event_shmem.h>

struct monad_event_thread_state;
struct monad_event_payload_page;

// Allocate event payload memory from a payload page, and fill in the event
// descriptor to refer to it
static void *_monad_event_alloc_payload(
    struct monad_event_payload_page **, struct monad_event_descriptor *,
    size_t payload_size, uint8_t source_id);

// Allocate memory from a payload page; used to directly allocate chunks from
// the metadata page
static void *_monad_event_alloc_from_fixed_page(
    struct monad_event_payload_page *, size_t payload_size, uint32_t *offset);

// Set an event descriptor to reference an object in the metadata page,
// allocated via an earlier call to `_monad_event_alloc_from_fixed_page`
static void _monad_event_set_metadata_descriptor_payload(
    void const *ptr, size_t size, struct monad_event_descriptor *event);

TAILQ_HEAD(monad_event_payload_page_queue, monad_event_payload_page);

// Event payloads live on slabs of memory called "payload pages". Each thread
// caches an active page in a thread_local so it can allocate without locking,
// and when it fills up a new page is taken from this pool
struct monad_event_payload_page_pool
{
    alignas(64) monad_spinlock_t lock;
    struct monad_event_payload_page_queue active_pages;
    struct monad_event_payload_page_queue free_pages;
    struct monad_event_payload_page **all_pages;
    size_t active_page_count;
    size_t free_page_count;
    size_t pages_allocated;
};

// Multi-producer, single-consumer queue used by the recorder
struct monad_event_recorder_queue
{
    alignas(64) _Atomic(uint64_t) prod_head;
    alignas(64) _Atomic(uint64_t) prod_tail;
    alignas(64) _Atomic(uint64_t) consume_next;
    alignas(64) size_t capacity;
    size_t capacity_mask;
    struct monad_event_descriptor *descriptor_table;
};

// Global state for the event recorder; owns the MPSC event descriptor queue,
// the payload page pool, all the thread-local state objects, and the global
// domain enable mask
struct monad_event_recorder
{
    struct monad_event_recorder_queue recorder_queue;
    uint64_t thread_source_ids;
    pthread_key_t thread_state_key;
    alignas(64) _Atomic(uint64_t) domain_enable_mask;
    alignas(64) atomic_bool initialized;
    alignas(64) monad_spinlock_t lock;
    TAILQ_HEAD(, monad_event_thread_state) thread_states;
    struct monad_event_payload_page_pool payload_page_pool;
    struct monad_event_payload_page *metadata_page;
    struct monad_event_thread_info *thread_info;
    uint64_t process_id;
};

extern struct monad_event_recorder g_monad_event_recorder;

// This structure appears at the start of the shared memory region for an
// event payload page; the `page_header` field is also understood by the client
// library; the rest is internal allocator book-keeping for the producer
struct monad_event_payload_page
{
    struct monad_event_payload_page_header page_header;
    uint8_t *heap_begin;
    uint8_t *heap_next;
    uint8_t *heap_end;
    uint64_t event_count;
    struct monad_event_payload_page_pool *page_pool;
    TAILQ_ENTRY(monad_event_payload_page) page_link;
    int memfd;
    char page_name[20];
};

// To make recording as fast as possible, some of the recorder state is cached
// in this thread-local object; namely, each thread has its own active payload
// page that it can allocate event payloads from without locking the page pool
struct monad_event_thread_state
{
    uint8_t source_id;
    struct monad_event_payload_page *payload_page;
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

inline uint64_t monad_event_recorder_set_domain_mask(uint64_t domain_mask)
{
    // The common case, which must be fast: we're changing the mask after
    // all initialization has been performed
    if (MONAD_LIKELY(atomic_load_explicit(
            &g_monad_event_recorder.initialized, memory_order_relaxed))) {
        return atomic_exchange_explicit(
            &g_monad_event_recorder.domain_enable_mask,
            domain_mask,
            memory_order_acq_rel);
    }

    // The slow, rare case: the recorder is not initialized, see
    // event_recorder.c
    extern uint64_t _monad_event_recorder_set_domain_mask_slow(uint64_t);
    return _monad_event_recorder_set_domain_mask_slow(domain_mask);
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
    #error cannot enable this yet; missing TSC HZ to ns mapping logic
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
    struct monad_event_payload_page **page_p,
    struct monad_event_descriptor *event, size_t payload_size,
    uint8_t source_id)
{
    struct monad_event_payload_page *page;
    void *payload;

    // When a payload page is full, the thread allocator calls this routine to
    // return it to page pool and request a new page; see event_recorder.c
    extern struct monad_event_payload_page *_monad_event_recorder_switch_page(
        struct monad_event_payload_page *);

    page = *page_p;
    MONAD_DEBUG_ASSERT(page != nullptr);
    if (MONAD_UNLIKELY(page->heap_next + payload_size > page->heap_end)) {
        // Not enough memory left on this page; switch to a free page
        page = *page_p = _monad_event_recorder_switch_page(page);
    }

    // Fill in the descriptor with the payload memory details
    event->payload_page = page->page_header.page_id;
    event->offset = (uint32_t)(page->heap_next - (uint8_t *)page);
    event->length = payload_size & 0x7FFFFFUL;
    event->source_id = source_id;
    event->page_generation = atomic_load_explicit(
        &page->page_header.page_generation, memory_order_relaxed);

    // Set the payload pointer and mark the space as allocated in the event page
    payload = page->heap_next;
    page->heap_next += payload_size;
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

inline void _monad_event_set_metadata_descriptor_payload(
    void const *ptr, size_t size, struct monad_event_descriptor *event)
{
    struct monad_event_payload_page const *const metadata_page =
        g_monad_event_recorder.metadata_page;
    event->payload_page = metadata_page->page_header.page_id;
    event->offset = (uint32_t)((uint8_t *)ptr - (uint8_t *)metadata_page);
    event->length = size & 0x7FFFFFUL;
    event->page_generation = atomic_load_explicit(
        &metadata_page->page_header.page_generation, memory_order_relaxed);
}

inline void _monad_event_recorder_queue_write(
    struct monad_event_recorder_queue *rq, struct monad_event_descriptor *event)
{
    // Write an event descriptor to the multi-producer, single-consume queue.
    // See the DPDK Programmer's Guide [4.5. Anatomy of a Ring Buffer] for
    // an explanation of how the multi-producer scheme works. This is needed
    // because events are written from multiple worker threads without locking.
    // Note that we don't read `ring->consume_next` here at all, because we
    // overwrite stale items rather than busy-wait on the queue draining. It is
    // the consumer's job to keep up, and it can detect over-writes using the
    // sequence number. The consumer lives in `event_session.c`, and is loop
    // that copies descriptors into subscriber queues.
    uint64_t prod_tail;
    uint64_t prod_next;

    // Claim ownership of the `prod_head` descriptor
    uint64_t const prod_head =
        atomic_fetch_add_explicit(&rq->prod_head, 1, memory_order_relaxed);
    prod_next = prod_head + 1;

    // Copy the event descriptor into the descriptor table
    event->seqno = prod_next;
    rq->descriptor_table[prod_head & rq->capacity_mask] = *event;

    // Move the tail to reflect the produced `prod_head` value
    prod_tail = prod_head;
    while (!atomic_compare_exchange_weak_explicit(
        &rq->prod_tail,
        &prod_tail,
        prod_next,
        memory_order_acq_rel,
        memory_order_relaxed)) {
        prod_tail = prod_head;
        monad_spinloop_hint();
    }
}

inline void monad_event_record(
    enum monad_event_type event_type, uint8_t flags, void const *payload,
    size_t payload_size)
{
    struct monad_event_descriptor event;
    struct monad_event_thread_state *thread_state;
    uint64_t domain_enable_bit;
    uint64_t domain_enable_mask;
    void *dst;

    domain_enable_bit = MONAD_EVENT_DOMAIN_MASK(MONAD_EVENT_DOMAIN(event_type));
    domain_enable_mask = atomic_load_explicit(
        &g_monad_event_recorder.domain_enable_mask, memory_order_acquire);
    if (MONAD_UNLIKELY((domain_enable_mask & domain_enable_bit) == 0)) {
        // Event's domain is not enabled
        return;
    }

    // Get the thread state immediately, before taking the timestamp. Although
    // this distorts the timestamp a bit, it this prevents time appearing to go
    // backwards on the thread with respect to the THREAD_CREATE event
    thread_state = _monad_event_get_thread_state();
    event.epoch_nanos = monad_event_timestamp();
    event.type = event_type;
    event.pop_scope = flags & MONAD_EVENT_POP_SCOPE ? 1U : 0U;
    dst = _monad_event_alloc_payload(
        &thread_state->payload_page,
        &event,
        payload_size,
        thread_state->source_id);
    memcpy(dst, payload, payload_size);
    _monad_event_recorder_queue_write(
        &g_monad_event_recorder.recorder_queue, &event);
}

static inline struct monad_event_payload_page **
_monad_event_get_payload_page_pool_array(size_t *size)
{
    // TODO(ken): this is a hack for now, for consumers in the same process;
    //   maybe it should have a better API?
    struct monad_event_payload_page **all_pages;
    struct monad_event_payload_page_pool *const page_pool =
        &g_monad_event_recorder.payload_page_pool;

    MONAD_SPINLOCK_LOCK(&page_pool->lock);
    if (size != nullptr) {
        *size = page_pool->active_page_count + page_pool->free_page_count;
    }
    all_pages = page_pool->all_pages;
    MONAD_SPINLOCK_UNLOCK(&page_pool->lock);
    return all_pages;
}
