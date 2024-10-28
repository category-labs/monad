#include <errno.h>
#include <stdarg.h>
#include <stdatomic.h>
#include <stdbit.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include <pthread.h>
#include <unistd.h>

#include <sys/mman.h>
#include <sys/queue.h>

#include <monad/core/assert.h>
#include <monad/core/srcloc.h>
#include <monad/core/tl_tid.h>
#include <monad/event/event.h>
#include <monad/event/event_recorder.h>
#include <monad/event/event_shared.h>
#include <monad/event/event_shmem.h>

extern char const *__progname;
static thread_local char g_error_buf[1024];
thread_local struct monad_event_thread_state g_tls_monad_thread_state;
struct monad_event_recorder g_monad_event_recorder;

__attribute__((format(printf, 3, 4))) static int format_errc(
    monad_source_location_t const *srcloc, int err, char const *format, ...)
{
    int rc;
    va_list ap;
    va_start(ap, format);
    rc = _monad_event_vformat_err(
        g_error_buf, sizeof g_error_buf, srcloc, err, format, ap);
    va_end(ap);
    return rc;
}

#define FORMAT_ERRC(...)                                                       \
    format_errc(&MONAD_SOURCE_LOCATION_CURRENT(), __VA_ARGS__)

/*
 * Page pool functions
 */

static int configure_payload_page_pool(
    struct monad_event_payload_page_pool *page_pool, size_t payload_page_size,
    uint16_t payload_page_count)
{
    char name[20];
    int memfd;
    struct monad_event_payload_page *page;

    memset(page_pool, 0, sizeof *page_pool);
    monad_spinlock_init(&page_pool->lock);
    TAILQ_INIT(&page_pool->active_pages);
    TAILQ_INIT(&page_pool->free_pages);
    page_pool->all_pages = calloc(payload_page_count, sizeof page);
    if (page_pool->all_pages == nullptr) {
        return FORMAT_ERRC(
            errno, "calloc(3) couldn't allocate direct access page array");
    }

    for (uint16_t p = 0; p < payload_page_count; ++p) {
        snprintf(name, sizeof name, "epp:%d:%hu", getpid(), p);
        memfd = memfd_create(name, MFD_CLOEXEC | MFD_HUGETLB);
        if (memfd == -1) {
            return FORMAT_ERRC(errno, "memfd_create(2) failed for %s", name);
        }
        if (ftruncate(memfd, (off_t)payload_page_size) == -1) {
            return FORMAT_ERRC(errno, "ftruncate(2) failed for %s", name);
        }
        page = mmap(
            nullptr,
            payload_page_size,
            PROT_WRITE,
            MAP_SHARED | MAP_HUGETLB | MAP_POPULATE,
            memfd,
            0);
        if (page == MAP_FAILED) {
            return FORMAT_ERRC(errno, "mmap(2) unable to map %s", name);
        }

        page->page_header.page_id = p;
        page->page_header.page_generation = 0;
        page->heap_next = page->heap_begin = (uint8_t *)(page + 1);
        page->heap_end = (uint8_t *)page + payload_page_size;
        page->memfd = memfd;
        page->page_pool = page_pool;
        strncpy(page->page_name, name, sizeof page->page_name);

        TAILQ_INSERT_TAIL(&page_pool->free_pages, page, page_link);
        page_pool->all_pages[p] = page;
        ++page_pool->free_page_count;
    }

    return 0;
}

static void
cleanup_payload_page_pool(struct monad_event_payload_page_pool *page_pool)
{
    struct monad_event_payload_page *page;
    MONAD_SPINLOCK_LOCK(&page_pool->lock);
    TAILQ_CONCAT(&page_pool->free_pages, &page_pool->active_pages, page_link);
    while ((page = TAILQ_FIRST(&page_pool->free_pages)) != nullptr) {
        (void)close(page->memfd);
        TAILQ_REMOVE(&page_pool->free_pages, page, page_link);
        (void)munmap(page, (size_t)(page->heap_end - (uint8_t *)page));
    }
    free(page_pool->all_pages);
    page_pool->all_pages = nullptr;
    page_pool->active_page_count = page_pool->free_page_count = 0;
    MONAD_SPINLOCK_UNLOCK(&page_pool->lock);
}

static struct monad_event_payload_page *
alloc_payload_page(struct monad_event_payload_page_pool *page_pool)
{
    struct monad_event_payload_page *page;
    MONAD_DEBUG_ASSERT(monad_spinlock_is_self_owned(&page_pool->lock));

    if (MONAD_UNLIKELY(page_pool->free_page_count <= 1)) {
        // This is fatal; even if there are a lot of events happening, low
        // page memory should result in pages being recycled faster, but not
        // coming close to running out.
        //
        // This will not happen as long as we have twice as many pages as there
        // are activate threads that want to record events (which is a
        // reasonable number).
        //
        // The reason we check for size 1 rather than empty is that when taking
        // the last page, we're allocating the "free" page we just finished
        // giving back, forcing all the events on this page to expire
        // immediately. This effectively makes the events useless to the
        // consumer immediately, and this fatal error is the wakeup call to
        // ensure the application runs with `num_pages >= 2 * num_threads`
        fprintf(
            stderr,
            "%s: exhausted all free payload pages (%lu in use)\n",
            __progname,
            page_pool->active_page_count);
        abort();
    }
    page = TAILQ_FIRST(&page_pool->free_pages);
    TAILQ_REMOVE(&page_pool->free_pages, page, page_link);
    TAILQ_INSERT_TAIL(&page_pool->active_pages, page, page_link);
    --page_pool->free_page_count;
    ++page_pool->active_page_count;

    // Mark this page as being reused, by incrementing the generation number
    // in its header; this effectively "poisons" all old event descriptors that
    // may still point into it that bear an older generation number
    atomic_fetch_add_explicit(
        &page->page_header.page_generation, 1, memory_order_release);

    page->heap_next = page->heap_begin = (uint8_t *)(page + 1);
    page->event_count = 0;
    ++page_pool->pages_allocated;
    return page;
}

static void free_payload_page(
    struct monad_event_payload_page_pool *page_pool,
    struct monad_event_payload_page *page)
{
    MONAD_DEBUG_ASSERT(monad_spinlock_is_self_owned(&page_pool->lock));

    // Deactivate the given page by placing it at the end of the free list.
    // The FIFO nature of the free list is critical to how our shared memory
    // strategy works. Note that it is still safe for the event consumer to
    // read from payload pages while they sit on the free list, and it will
    // remain safe until the page is recycled, once it reaches the head of the
    // free list. After it is recycled, the page will be marked as not safe to
    // read by incrementing its page generation number.
    TAILQ_REMOVE(&page_pool->active_pages, page, page_link);
    TAILQ_INSERT_TAIL(&page_pool->free_pages, page, page_link);
    --page_pool->active_page_count;
    ++page_pool->free_page_count;
}

struct monad_event_payload_page *
_monad_event_recorder_switch_page(struct monad_event_payload_page *page)
{
    struct monad_event_payload_page_pool *const page_pool = page->page_pool;
    MONAD_SPINLOCK_LOCK(&page_pool->lock);
    free_payload_page(page_pool, page);
    page = alloc_payload_page(page_pool);
    MONAD_SPINLOCK_UNLOCK(&page_pool->lock);
    // Manually inject a page allocation event descriptor into the new page
    MONAD_EVENT(MONAD_EVENT_THR_PAGE_ALLOC, 0);
    return page;
}

/*
 * Event recorder functions
 */

static void thread_state_dtor(void *arg0);

static void __attribute__((constructor(MONAD_EVENT_RECORDER_CTOR_PRIO)))
init_event_recorder()
{
    int rc;

    monad_spinlock_init(&g_monad_event_recorder.lock);
    TAILQ_INIT(&g_monad_event_recorder.thread_states);
    rc = pthread_key_create(
        &g_monad_event_recorder.thread_state_key, thread_state_dtor);
    if (rc != 0) {
        (void)FORMAT_ERRC(rc, "unable to create thread recorder pthread key");
        fprintf(
            stderr,
            "%s: fatal error in event recorder ctor: %s",
            __progname,
            g_error_buf);
        abort();
    }
    g_monad_event_recorder.process_id = (uint64_t)getpid();
}

static void __attribute__((destructor(MONAD_EVENT_RECORDER_CTOR_PRIO)))
cleanup_event_recorder()
{
    struct monad_event_payload_page_pool *const page_pool =
        &g_monad_event_recorder.payload_page_pool;
    struct monad_event_recorder_queue *const rq =
        &g_monad_event_recorder.recorder_queue;

    if (page_pool->all_pages != nullptr) {
        cleanup_payload_page_pool(page_pool);
    }
    pthread_key_delete(g_monad_event_recorder.thread_state_key);
    _monad_event_unmap_descriptor_table(rq->descriptor_table, rq->capacity);
}

static int
init_recorder_queue(struct monad_event_recorder_queue *rq, uint8_t ring_shift)
{
    int rc;
    int fd;
    rq->capacity = 1UL << ring_shift;
    rc = _monad_event_mmap_descriptor_table(
        MONAD_EVENT_RING_TYPE_RECORDER,
        ring_shift,
        "rec_mpsc",
        format_errc,
        &rq->descriptor_table,
        &rq->capacity,
        &fd);
    if (rc != 0) {
        return rc;
    }
    rq->capacity_mask = rq->capacity - 1;
    (void)close(fd);
    return 0;
}

static int configure_recorder_locked(
    uint8_t ring_shift, size_t payload_page_size, uint16_t payload_page_count)
{
    struct monad_event_payload_page_pool *page_pool;
    struct monad_event_payload_page *metadata_page;
    struct monad_event_recorder_queue *rq;
    int rc;

    MONAD_DEBUG_ASSERT(
        monad_spinlock_is_self_owned(&g_monad_event_recorder.lock));
    if (atomic_load_explicit(
            &g_monad_event_recorder.initialized, memory_order_acquire)) {
        return FORMAT_ERRC(
            EBUSY, "event recorder already running; cannot configure");
    }
    rq = &g_monad_event_recorder.recorder_queue;
    page_pool = &g_monad_event_recorder.payload_page_pool;
    if (page_pool->all_pages != nullptr) {
        // Reconfiguring; tear everything down and do it again
        _monad_event_unmap_descriptor_table(rq->descriptor_table, rq->capacity);
        cleanup_payload_page_pool(page_pool);
    }
    if (ring_shift == 0) {
        ring_shift = MONAD_EVENT_RECORDER_DEFAULT_RING_SHIFT;
    }
    if ((rc = init_recorder_queue(rq, ring_shift)) != 0) {
        return rc;
    }
    if ((rc = configure_payload_page_pool(
             page_pool, payload_page_size, payload_page_count)) != 0) {
        return rc;
    }

    // Allocate a special page to hold fixed metadata, which is never recycled
    MONAD_SPINLOCK_LOCK(&page_pool->lock);
    metadata_page = g_monad_event_recorder.metadata_page =
        alloc_payload_page(page_pool);
    MONAD_SPINLOCK_UNLOCK(&page_pool->lock);
    g_monad_event_recorder.thread_info = _monad_event_alloc_from_fixed_page(
        metadata_page,
        UINT8_MAX * sizeof g_monad_event_recorder.thread_info[0],
        nullptr);
    MONAD_ASSERT(g_monad_event_recorder.thread_info != nullptr);
    return 0;
}

int monad_event_recorder_configure(
    uint8_t ring_shift, size_t payload_page_size, uint16_t payload_page_count)
{
    int rc;

    if (ring_shift < MONAD_EVENT_RECORDER_MIN_RING_SHIFT ||
        ring_shift > MONAD_EVENT_RECORDER_MAX_RING_SHIFT) {
        return FORMAT_ERRC(
            ERANGE,
            "ring_shift out allowed range [%hhu, %hhu]: "
            "(ring sizes: [%lu, %lu])",
            MONAD_EVENT_RECORDER_MIN_RING_SHIFT,
            MONAD_EVENT_RECORDER_MAX_RING_SHIFT,
            (1UL << MONAD_EVENT_RECORDER_MIN_RING_SHIFT),
            (1UL << MONAD_EVENT_RECORDER_MAX_RING_SHIFT));
    }
    if (payload_page_size < MONAD_EVENT_MIN_PAYLOAD_PAGE_SIZE ||
        payload_page_size > MONAD_EVENT_MAX_PAYLOAD_PAGE_SIZE) {
        return FORMAT_ERRC(
            ERANGE,
            "payload_page_size must be between %lu "
            "and %lu",
            MONAD_EVENT_MIN_PAYLOAD_PAGE_SIZE,
            MONAD_EVENT_MAX_PAYLOAD_PAGE_SIZE);
    }
    if (payload_page_count < MONAD_EVENT_MIN_PAYLOAD_PAGE_COUNT) {
        return FORMAT_ERRC(
            ERANGE,
            "payload_page_count must be between %hu "
            "and %hu",
            MONAD_EVENT_MIN_PAYLOAD_PAGE_COUNT,
            UINT16_MAX);
    }

    MONAD_SPINLOCK_LOCK(&g_monad_event_recorder.lock);
    rc = configure_recorder_locked(
        ring_shift, payload_page_size, payload_page_count);
    MONAD_SPINLOCK_UNLOCK(&g_monad_event_recorder.lock);
    return rc;
}

char const *monad_event_recorder_get_last_error()
{
    return g_error_buf;
}

uint64_t _monad_event_recorder_set_domain_mask_slow(uint64_t domain_mask)
{
    extern void _monad_event_session_start_sync_thread(pthread_barrier_t *);
    pthread_barrier_t sync_ready_barrier;
    struct monad_event_payload_page_pool *page_pool;
    int rc;

    if (domain_mask == 0) {
        // No need to try initializing anything, we still do the exchange in
        // case we're racing
        goto Done;
    }

    rc = pthread_barrier_init(&sync_ready_barrier, nullptr, 2);
    if (rc != 0) {
        FORMAT_ERRC(rc, "unable to create sync barrier");
        fprintf(stderr, "%s: [fatal] %s\n", __progname, g_error_buf);
        abort();
    }

    page_pool = &g_monad_event_recorder.payload_page_pool;
    MONAD_SPINLOCK_LOCK(&g_monad_event_recorder.lock);
    if (page_pool->all_pages == nullptr) {
        rc = configure_recorder_locked(
            MONAD_EVENT_RECORDER_DEFAULT_RING_SHIFT,
            MONAD_EVENT_DEFAULT_PAYLOAD_PAGE_SIZE,
            MONAD_EVENT_DEFAULT_PAYLOAD_PAGE_COUNT);
        if (rc != 0 && rc != EBUSY) {
            fprintf(
                stderr,
                "%s: monad_event_recorder_configure failed while setting mask: "
                "%s\n",
                __progname,
                g_error_buf);
            abort();
        }
    }

    // Start the consumer thread and mark the recorder as initialized
    _monad_event_session_start_sync_thread(&sync_ready_barrier);
    atomic_store_explicit(
        &g_monad_event_recorder.initialized, true, memory_order_release);
    MONAD_SPINLOCK_UNLOCK(&g_monad_event_recorder.lock);

    // We don't change the enable mask until the sync thread is fully ready.
    // This must be called the event recorder lock released.
    (void)pthread_barrier_wait(&sync_ready_barrier);
    (void)pthread_barrier_destroy(&sync_ready_barrier);

Done:
    return atomic_exchange_explicit(
        &g_monad_event_recorder.domain_enable_mask,
        domain_mask,
        memory_order_acq_rel);
}

void monad_event_recorder_halt()
{
    atomic_store_explicit(&g_monad_event_recorder.domain_enable_mask, 0,
        memory_order_release);
    extern void _monad_event_session_wait_drain_queue();
    _monad_event_session_wait_drain_queue();
}

/*
 * Thread state functions
 */

static void thread_state_dtor(void *arg0)
{
    struct monad_event_payload_page *page;
    struct monad_event_payload_page_pool *page_pool;
    struct monad_event_thread_state *thread_state = arg0;

    // Record a final event, for the exiting of this thread
    monad_event_record(MONAD_EVENT_THREAD_EXIT, 0, nullptr, 0);

    // Give back the queue_id for this thread, and remove the thread's recorder
    // state object from the global list
    MONAD_SPINLOCK_LOCK(&g_monad_event_recorder.lock);
    g_monad_event_recorder.thread_source_ids &=
        ~(uint64_t)(1UL << (thread_state->source_id - 1));
    TAILQ_REMOVE(&g_monad_event_recorder.thread_states, thread_state, next);
    MONAD_SPINLOCK_UNLOCK(&g_monad_event_recorder.lock);

    // Deactivate the recorder's payload page
    page = thread_state->payload_page;
    MONAD_DEBUG_ASSERT(page != nullptr);
    page_pool = page->page_pool;
    MONAD_SPINLOCK_LOCK(&page_pool->lock);
    free_payload_page(page_pool, page);
    MONAD_SPINLOCK_UNLOCK(&page_pool->lock);
}

void _monad_event_init_thread_state(
    struct monad_event_thread_state *thread_state)
{
    struct monad_event_descriptor event;
    struct monad_event_payload_page_pool *page_pool;
    struct monad_event_thread_info local_thr_info;
    struct monad_event_thread_info *thr_info;
    unsigned s;

    memset(thread_state, 0, sizeof *thread_state);
    memset(&local_thr_info, 0, sizeof local_thr_info);
    local_thr_info.epoch_nanos = monad_event_get_epoch_nanos();
    local_thr_info.process_id = g_monad_event_recorder.process_id;
    local_thr_info.thread_id = thread_state->thread_id = (uint64_t)get_tl_tid();
    (void)pthread_getname_np(
        pthread_self(),
        local_thr_info.thread_name,
        sizeof local_thr_info.thread_name);

    // Allocate an active payload page for this thread recorder
    page_pool = &g_monad_event_recorder.payload_page_pool;
    MONAD_SPINLOCK_LOCK(&page_pool->lock);
    thread_state->payload_page = alloc_payload_page(page_pool);
    MONAD_SPINLOCK_UNLOCK(&page_pool->lock);

    // Reserve a source_id for this thread recorder, add it to the global list
    MONAD_SPINLOCK_LOCK(&g_monad_event_recorder.lock);
    // TOOD(ken): this gives us a maximum of 64 recording threads, but we have
    // enough bits in the event descriptor to support 256 threads
    s = stdc_first_trailing_zero(g_monad_event_recorder.thread_source_ids);
    if (s == 0) {
        fprintf(
            stderr,
            "%s: fatal error no space left in queue_id bitmap for "
            "new thread %s:%lu\n",
            __progname,
            local_thr_info.thread_name,
            local_thr_info.thread_id);
        abort();
    }
    local_thr_info.source_id = thread_state->source_id = (uint8_t)s;
    g_monad_event_recorder.thread_source_ids |= 1UL << (s - 1);

    // Copy local thread info into the metadata array that's present in shared
    // memory
    thr_info = &g_monad_event_recorder.thread_info[s];
    memcpy(thr_info, &local_thr_info, sizeof local_thr_info);
    TAILQ_INSERT_TAIL(
        &g_monad_event_recorder.thread_states, thread_state, next);
    pthread_setspecific(g_monad_event_recorder.thread_state_key, thread_state);
    MONAD_SPINLOCK_UNLOCK(&g_monad_event_recorder.lock);

    // Announce the creation of this thread
    event.type = MONAD_EVENT_THREAD_CREATE;
    event.epoch_nanos = thr_info->epoch_nanos;
    event.pop_scope = 0;
    event.source_id = thr_info->source_id;
    _monad_event_set_metadata_descriptor_payload(
        thr_info, sizeof *thr_info, &event);
    _monad_event_recorder_queue_write(
        &g_monad_event_recorder.recorder_queue, &event);

    // Remember the introducing sequence number
    thr_info->seqno = event.seqno;
}
