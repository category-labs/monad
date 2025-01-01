#include <errno.h>
#include <stdarg.h>
#include <stdatomic.h>
#include <stdbit.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <pthread.h>
#include <unistd.h>

#include <sys/mman.h>
#include <sys/queue.h>

#include <monad/core/assert.h>
#include <monad/core/spinlock.h>
#include <monad/core/srcloc.h>
#include <monad/core/tl_tid.h>
#include <monad/event/event.h>
#include <monad/event/event_iterator.h>
#include <monad/event/event_protocol.h>
#include <monad/event/event_recorder.h>
#include <monad/event/event_shared.h>
#include <monad/event/event_types.h>

static thread_local char g_error_buf[1024];
static size_t const PAGE_2MB = 1UL << 21; // x64 2MiB large page

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

static int mmap_payload_page(
    char const *name, size_t size, uint16_t page_id,
    struct monad_event_payload_page **page_p)
{
    int memfd;
    struct monad_event_payload_page *page;

    memfd = memfd_create(name, MFD_CLOEXEC | MFD_HUGETLB);
    if (memfd == -1) {
        return FORMAT_ERRC(errno, "memfd_create(2) failed for %s", name);
    }
    if (ftruncate(memfd, (off_t)size) == -1) {
        return FORMAT_ERRC(errno, "ftruncate(2) failed for %s", name);
    }
    page = *page_p = mmap(
        nullptr,
        size,
        PROT_WRITE,
        MAP_SHARED | MAP_HUGETLB | MAP_POPULATE,
        memfd,
        0);
    if (page == MAP_FAILED) {
        return FORMAT_ERRC(errno, "mmap(2) unable to map %s", name);
    }

    atomic_store_explicit(&page->overwrite_seqno, 0, memory_order_relaxed);
    page->page_id = page_id;
    page->page_base = (uint8_t *)page;
    page->heap_next = page->heap_begin = (uint8_t *)(page + 1);
    page->heap_end = page->page_base + size;
    page->memfd = memfd;
    (void)strlcpy(page->page_name, name, sizeof page->page_name);
    page->page_name[sizeof page->page_name - 1] = '\0';
    return 0;
}

static int configure_payload_page_pool(
    struct monad_event_payload_page_pool *page_pool, uint8_t payload_page_shift,
    uint16_t payload_page_count, _Atomic(uint64_t) const *last_seqno)
{
    char name[20];
    int rc;
    struct monad_event_payload_page *page;
    size_t const payload_page_size = 1UL << payload_page_shift;

    memset(page_pool, 0, sizeof *page_pool);
    monad_spinlock_init(&page_pool->lock);
    TAILQ_INIT(&page_pool->active_pages);
    TAILQ_INIT(&page_pool->free_pages);
    for (uint16_t p = 0; p < payload_page_count; ++p) {
        // The "+ 1" bias to the page IDs is because page ID 0 is the shared
        // metadata page
        snprintf(name, sizeof name, "epp:%d:%hu", getpid(), p + 1);
        if ((rc = mmap_payload_page(name, payload_page_size, p + 1, &page)) !=
            0) {
            return rc;
        }
        page->page_pool = page_pool;
        TAILQ_INSERT_TAIL(&page_pool->free_pages, page, page_link);
        ++page_pool->free_page_count;
    }
    page_pool->last_seqno = last_seqno;

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
        (void)munmap(page, (size_t)(page->heap_end - page->page_base));
    }
    page_pool->active_page_count = page_pool->free_page_count = 0;
    page_pool->last_seqno = nullptr;
    MONAD_SPINLOCK_UNLOCK(&page_pool->lock);
}

static struct monad_event_payload_page *
activate_payload_page(struct monad_event_payload_page_pool *page_pool)
{
    struct monad_event_payload_page *page;
    MONAD_DEBUG_ASSERT(monad_spinlock_is_self_owned(&page_pool->lock));

    // Assert that we have more than one page free, otherwise it's fatal; even
    // if there are a lot of events happening, low page memory should result in
    // pages being recycled faster, but not coming close to running out.
    //
    // This will not happen as long as we have twice as many pages as there are
    // activate threads that want to record events (which is a reasonable
    // number).
    //
    // The reason we check for size 1 rather than empty is that when taking the
    // last page, we're allocating the "free" page we just finished giving back,
    // forcing all the events on this page to expire immediately. This
    // effectively makes the events useless to the consumer immediately, so
    // this fatal error is the wakeup call to ensure the application runs with
    // `num_pages >= 2 * num_threads`
    MONAD_ASSERT_PRINTF(
        page_pool->free_page_count > 1,
        "exhausted all free payload pages (%lu in use)",
        page_pool->active_page_count);
    page = TAILQ_FIRST(&page_pool->free_pages);
    TAILQ_REMOVE(&page_pool->free_pages, page, page_link);
    TAILQ_INSERT_TAIL(&page_pool->active_pages, page, page_link);
    --page_pool->free_page_count;
    ++page_pool->active_page_count;

    // Mark this page as being reused, by stamping it with the approximate
    // current sequence number; this effectively "poisons" all old event
    // descriptors that may still point into it that bear an older sequence
    // number. The fact that it's approximate is fine, because this page has
    // been expired for a while.
    atomic_store_explicit(
        &page->overwrite_seqno,
        atomic_load_explicit(page_pool->last_seqno, memory_order_acquire),
        memory_order_release);

    page->heap_next = page->heap_begin;
    page->event_count = 0;
    ++page->alloc_count;
    ++page_pool->pages_allocated;
    return page;
}

static void deactivate_payload_page(
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
    // read by recording in the header the sequence number when it was recycled.
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
    deactivate_payload_page(page_pool, page);
    page = activate_payload_page(page_pool);
    MONAD_SPINLOCK_UNLOCK(&page_pool->lock);
    return page;
}

struct monad_event_payload_page *_monad_event_activate_payload_page(
    struct monad_event_payload_page_pool *page_pool)
{
    struct monad_event_payload_page *page;
    MONAD_SPINLOCK_LOCK(&page_pool->lock);
    page = activate_payload_page(page_pool);
    MONAD_SPINLOCK_UNLOCK(&page_pool->lock);
    return page;
}

/*
 * Event ring functions
 */

void cleanup_event_ring(
    struct monad_event_ring *ring, int *control_fd, int *descriptor_table_fd)
{
    size_t const desc_table_map_len =
        ring->capacity * sizeof(struct monad_event_descriptor);
    if (ring->control != nullptr) {
        munmap(ring->control, (size_t)getpagesize());
        (void)close(*control_fd);
        *control_fd = -1;
    }
    if (ring->descriptor_table != nullptr) {
        munmap(ring->descriptor_table, desc_table_map_len);
        munmap(
            (uint8_t *)ring->descriptor_table + desc_table_map_len, PAGE_2MB);
        (void)close(*descriptor_table_fd);
        *descriptor_table_fd = -1;
    }
}

int init_event_ring(
    struct monad_event_ring *ring, enum monad_event_ring_type ring_type,
    uint8_t ring_shift, int *control_fd, int *descriptor_table_fd)
{
    size_t mmap_page_size;
    size_t desc_table_map_len;
    int saved_error;
    char name[32];

    memset(ring, 0, sizeof *ring);
    *control_fd = -1;
    *descriptor_table_fd = -1;

    // Map the ring control structure (a single, minimum-sized VM page)
    mmap_page_size = (size_t)getpagesize();
    snprintf(name, sizeof name, "evt_rc:%d:%hhu", getpid(), ring_type);
    *control_fd = memfd_create(name, MFD_CLOEXEC);
    if (*control_fd == -1) {
        saved_error = FORMAT_ERRC(errno, "memfd_create(2) failed for %s", name);
        goto Error;
    }
    if (ftruncate(*control_fd, (off_t)mmap_page_size) == -1) {
        saved_error = FORMAT_ERRC(errno, "ftruncate(2) failed for %s", name);
        goto Error;
    }
    ring->control = mmap(
        nullptr,
        mmap_page_size,
        PROT_READ | PROT_WRITE,
        MAP_SHARED,
        *control_fd,
        0);
    if (ring->control == MAP_FAILED) {
        saved_error = FORMAT_ERRC(errno, "mmap(2) unable to map %s", name);
        goto Error;
    }

    // Map the ring descriptor table; this uses huge pages and also the
    // "wrap-around" technique. If the ring size is too small, we need to
    // round the ring_size up such that it fill an entire 2MB page.
    ring->capacity = 1UL << ring_shift;
    desc_table_map_len = ring->capacity * sizeof(struct monad_event_descriptor);
    if (desc_table_map_len < PAGE_2MB) {
        desc_table_map_len = PAGE_2MB;
        ring->capacity =
            desc_table_map_len / sizeof(struct monad_event_descriptor);
        MONAD_ASSERT(stdc_has_single_bit(ring->capacity));
    }
    snprintf(name, sizeof name, "evt_rdt:%d:%hhu", getpid(), ring_type);
    *descriptor_table_fd = memfd_create(name, MFD_CLOEXEC | MFD_HUGETLB);
    if (*descriptor_table_fd == -1) {
        saved_error = FORMAT_ERRC(errno, "memfd_create(2) failed for %s", name);
        goto Error;
    }
    if (ftruncate(*descriptor_table_fd, (off_t)desc_table_map_len) == -1) {
        saved_error = FORMAT_ERRC(errno, "ftruncate(2) failed for %s", name);
        goto Error;
    }

    // First, reserve a single anonymous mapping whose size encompasses both
    // the nominal size of the descriptor table plus the size of the
    // wrap-around large page. We'll remap the memfd into this reserved range
    // later, using MAP_FIXED.
    ring->descriptor_table = mmap(
        nullptr,
        desc_table_map_len + PAGE_2MB,
        PROT_READ | PROT_WRITE,
        MAP_SHARED | MAP_ANONYMOUS | MAP_HUGETLB,
        -1,
        0);
    if (ring->descriptor_table == MAP_FAILED) {
        saved_error = FORMAT_ERRC(errno, "mmap(2) unable to map %s", name);
        goto Error;
    }

    // Map the descriptor table into the first part of the space we just
    // reserved
    if (mmap(
            ring->descriptor_table,
            desc_table_map_len,
            PROT_READ | PROT_WRITE,
            MAP_SHARED | MAP_FIXED | MAP_HUGETLB | MAP_POPULATE,
            *descriptor_table_fd,
            0) == MAP_FAILED) {
        saved_error = FORMAT_ERRC(
            errno,
            "unable to remap descriptor table range to memfd for %s",
            name);
        goto Error;
    }

    // Map the "wrap around" large page after the descriptor table. This causes
    // the first large page of the table to be mapped immediately after the end
    // of the table, allowing us to naturally "wrap around" in memory by the
    // size of one full large page. Thus we can bulk memcpy(3) event
    // descriptors safely near the end of the table, and it will wrap around
    // in memory without doing any error-prone index massaging.
    if (mmap(
            (uint8_t *)ring->descriptor_table + desc_table_map_len,
            PAGE_2MB,
            PROT_READ | PROT_WRITE,
            MAP_SHARED | MAP_FIXED | MAP_HUGETLB | MAP_POPULATE,
            *descriptor_table_fd,
            0) == MAP_FAILED) {
        saved_error = FORMAT_ERRC(
            errno, "mmap(2) wrap-around mapping for %s failed", name);
        goto Error;
    }

    // Despite the MAP_POPULATE, we don't necessarily trust that everything
    // is ready yet; "warm up" the mappings by zeroing out the entire range
    memset(ring->descriptor_table, 0, desc_table_map_len + PAGE_2MB);
    ring->capacity_mask = ring->capacity - 1;
    return 0;

Error:
    cleanup_event_ring(ring, control_fd, descriptor_table_fd);
    return saved_error;
}

/*
 * Event recorder functions
 */

struct monad_event_recorder g_monad_event_recorders[MONAD_EVENT_RING_COUNT];

struct monad_event_recorder_shared_state g_monad_event_recorder_shared_state;

static void thread_cache_dtor(void *arg0);

static void __attribute__((constructor(MONAD_EVENT_RECORDER_CTOR_PRIO)))
init_event_recorders()
{
    int rc;
    char name[20];
    struct monad_event_recorder *recorder;
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;

    monad_spinlock_init(&rss->lock);
    TAILQ_INIT(&rss->thread_caches);
    rc = pthread_key_create(&rss->thread_cache_key, thread_cache_dtor);
    MONAD_ASSERT_PRINTF(
        rc == 0, "unable to create thread recorder pthread key, error: %d", rc);

    snprintf(name, sizeof name, "epp_meta_%d", getpid());
    // Allocate a special page to hold fixed metadata, which is shared by
    // all recorders and never recycled
    rc = mmap_payload_page(name, PAGE_2MB, 0, &rss->metadata_page);
    ++rss->metadata_page->alloc_count;
    MONAD_ASSERT_PRINTF(rc == 0, "unable to mmap metadata page, error: %d", rc);
    rss->thread_info_table = _monad_event_alloc_from_fixed_page(
        rss->metadata_page,
        (UINT8_MAX + 1) * sizeof rss->thread_info_table[0],
        nullptr);
    MONAD_ASSERT(rss->thread_info_table != nullptr);
    rss->block_header_table = _monad_event_alloc_from_fixed_page(
        rss->metadata_page,
        (1U << 12) * sizeof rss->block_header_table[0],
        nullptr);
    MONAD_ASSERT(rss->block_header_table != nullptr);
    rss->process_id = (uint64_t)getpid();

    for (uint8_t q = 0; q < MONAD_EVENT_RING_COUNT; ++q) {
        recorder = &g_monad_event_recorders[q];
        memset(recorder, 0, sizeof *recorder);
        monad_spinlock_init(&recorder->lock);
        recorder->ring_type = q;
        recorder->control_fd = recorder->descriptor_table_fd = -1;
    }
}

static void __attribute__((destructor(MONAD_EVENT_RECORDER_CTOR_PRIO)))
cleanup_event_recorders()
{
    struct monad_event_recorder *recorder;
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;

    for (uint8_t q = 0; q < MONAD_EVENT_RING_COUNT; ++q) {
        recorder = &g_monad_event_recorders[q];
        cleanup_event_ring(
            &recorder->event_ring,
            &recorder->control_fd,
            &recorder->descriptor_table_fd);
        cleanup_payload_page_pool(&recorder->payload_page_pool);
    }
    pthread_key_delete(rss->thread_cache_key);
}

static int configure_recorder_locked(
    struct monad_event_recorder *recorder, uint8_t ring_shift,
    uint8_t payload_page_shift, uint16_t payload_page_count)
{
    int rc;
    struct monad_event_payload_page *page;
    struct monad_event_payload_page_pool *page_pool;

    MONAD_DEBUG_ASSERT(monad_spinlock_is_self_owned(&recorder->lock));
    if (atomic_load_explicit(&recorder->enabled, memory_order_acquire)) {
        return FORMAT_ERRC(
            EBUSY, "event recorder already running; cannot configure");
    }
    page_pool = &recorder->payload_page_pool;
    if (recorder->all_pages != nullptr) {
        // Reconfiguring; tear everything down and do it again
        cleanup_event_ring(
            &recorder->event_ring,
            &recorder->control_fd,
            &recorder->descriptor_table_fd);
        cleanup_payload_page_pool(page_pool);
        free(recorder->all_pages);
        recorder->all_pages = nullptr;
    }
    recorder->all_pages_size = payload_page_count + 1;
    recorder->all_pages = calloc(recorder->all_pages_size, sizeof page);
    if (recorder->all_pages == nullptr) {
        return FORMAT_ERRC(errno, "calloc for all_pages array failed");
    }
    recorder->all_pages[0] = g_monad_event_recorder_shared_state.metadata_page;
    if (ring_shift == 0) {
        ring_shift = MONAD_EVENT_DEFAULT_RING_SHIFT;
    }
    if ((rc = init_event_ring(
             &recorder->event_ring,
             recorder->ring_type,
             ring_shift,
             &recorder->control_fd,
             &recorder->descriptor_table_fd)) != 0) {
        free(recorder->all_pages);
        recorder->all_pages_size = 0;
        return rc;
    }
    if ((rc = configure_payload_page_pool(
             page_pool,
             payload_page_shift,
             payload_page_count,
             &recorder->event_ring.control->last_seqno)) != 0) {
        cleanup_event_ring(
            &recorder->event_ring,
            &recorder->control_fd,
            &recorder->descriptor_table_fd);
        free(recorder->all_pages);
        recorder->all_pages_size = 0;
        return rc;
    }
    TAILQ_FOREACH(page, &page_pool->free_pages, page_link)
    {
        recorder->all_pages[page->page_id] = page;
    }
    return 0;
}

// Set an event descriptor to reference an object in the metadata page,
// allocated via an earlier call to `_monad_event_alloc_from_fixed_page`
static void set_metadata_descriptor_payload(
    void const *ptr, size_t size, struct monad_event_descriptor *event)
{
    struct monad_event_payload_page const *const metadata_page =
        g_monad_event_recorder_shared_state.metadata_page;
    event->payload_page = metadata_page->page_id;
    event->offset = (uint32_t)((uint8_t *)ptr - (uint8_t *)metadata_page);
    event->length = size & 0x7FFFFFUL;
}

int monad_event_recorder_configure(
    enum monad_event_ring_type ring_type, uint8_t ring_shift,
    uint8_t payload_page_shift, uint16_t payload_page_count)
{
    int rc;
    struct monad_event_recorder *recorder;

    if (ring_type >= MONAD_EVENT_RING_COUNT) {
        return FORMAT_ERRC(
            EINVAL, "ring_type %hhu is not a valid value", ring_type);
    }
    if (ring_shift < MONAD_EVENT_MIN_RING_SHIFT ||
        ring_shift > MONAD_EVENT_MAX_RING_SHIFT) {
        return FORMAT_ERRC(
            ERANGE,
            "ring_shift outside allowed range [%hhu, %hhu]: "
            "(ring sizes: [%lu, %lu])",
            MONAD_EVENT_MIN_RING_SHIFT,
            MONAD_EVENT_MAX_RING_SHIFT,
            (1UL << MONAD_EVENT_MIN_RING_SHIFT),
            (1UL << MONAD_EVENT_MAX_RING_SHIFT));
    }
    if (payload_page_shift < MONAD_EVENT_MIN_PAYLOAD_PAGE_SHIFT ||
        payload_page_shift > MONAD_EVENT_MAX_PAYLOAD_PAGE_SHIFT) {
        return FORMAT_ERRC(
            ERANGE,
            "payload_page_shift outside allowed range [%hhu, %hhu]: "
            "(page sizes: [%lu, %lu])",
            MONAD_EVENT_MIN_PAYLOAD_PAGE_SHIFT,
            MONAD_EVENT_MAX_PAYLOAD_PAGE_SHIFT,
            (1UL << MONAD_EVENT_MIN_PAYLOAD_PAGE_SHIFT),
            (1UL << MONAD_EVENT_MAX_PAYLOAD_PAGE_SHIFT));
    }
    if (payload_page_count < MONAD_EVENT_MIN_PAYLOAD_PAGE_COUNT) {
        return FORMAT_ERRC(
            ERANGE,
            "payload_page_count must be between %hu "
            "and %hu",
            MONAD_EVENT_MIN_PAYLOAD_PAGE_COUNT,
            UINT16_MAX);
    }

    recorder = &g_monad_event_recorders[ring_type];
    MONAD_SPINLOCK_LOCK(&recorder->lock);
    rc = configure_recorder_locked(
        recorder, ring_shift, payload_page_shift, payload_page_count);
    MONAD_SPINLOCK_UNLOCK(&recorder->lock);
    return rc;
}

bool _monad_event_recorder_set_enabled_slow(
    struct monad_event_recorder *recorder, bool enabled)
{
    int rc;
    if (!enabled) {
        // Not initialized but still not being enabled, just do nothing
        return false;
    }
    // The initialization flag itself is indicated by an atomic, but the
    // initialization process itself is protected by the lock -- the lock
    // must be held to change the value of the `initialized` atomic, and to
    // touch any of the configurable objects
    MONAD_SPINLOCK_LOCK(&recorder->lock);
    if (atomic_load_explicit(&recorder->initialized, memory_order_acquire)) {
        // Lost a lock race to become the initializer. Skip to Initialized
        goto Initialized;
    }
    if (recorder->all_pages == nullptr) {
        rc = configure_recorder_locked(
            recorder,
            MONAD_EVENT_DEFAULT_RING_SHIFT,
            MONAD_EVENT_DEFAULT_PAYLOAD_PAGE_SHIFT,
            MONAD_EVENT_DEFAULT_PAYLOAD_PAGE_COUNT);
        MONAD_ASSERT_PRINTF(
            rc == 0 || rc == EBUSY,
            "monad_event_recorder_configure failed for %hhu with error: %d",
            recorder->ring_type,
            rc);
    }
    atomic_store_explicit(&recorder->initialized, true, memory_order_release);
Initialized:
    MONAD_SPINLOCK_UNLOCK(&recorder->lock);
    enabled = atomic_exchange_explicit(
        &recorder->enabled, true, memory_order_acq_rel);
    monad_event_record(recorder, MONAD_EVENT_RING_INIT, 0, nullptr, 0);
    return enabled;
}

char const *monad_event_recorder_get_last_error()
{
    return g_error_buf;
}

/*
 * Thread cache functions
 */

thread_local struct monad_event_recorder_thr g_tls_monad_recorder_thread_cache;

static void thread_cache_dtor(void *arg0)
{
    struct monad_event_payload_page *page;
    struct monad_event_payload_page_pool *page_pool;
    struct monad_event_recorder_thr *const thread_cache = arg0;
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;

    // Record a final event, for the exiting of this thread
    for (uint8_t q = 0; q < MONAD_EVENT_RING_COUNT; ++q) {
        monad_event_record(
            &g_monad_event_recorders[q],
            MONAD_EVENT_THREAD_EXIT,
            0,
            nullptr,
            0);
    }

    // Give back the source_id for this thread, and remove the thread's recorder
    // state object from the global list
    MONAD_SPINLOCK_LOCK(&rss->lock);
    rss->thread_source_ids &= ~(uint64_t)(1UL << (thread_cache->source_id - 1));
    TAILQ_REMOVE(&rss->thread_caches, thread_cache, next);
    MONAD_SPINLOCK_UNLOCK(&rss->lock);

    // Deactivate the recorder's payload pages
    for (uint8_t q = 0; q < MONAD_EVENT_RING_COUNT; ++q) {
        page = thread_cache->payload_page[q];
        if (page != nullptr) {
            page_pool = page->page_pool;
            MONAD_SPINLOCK_LOCK(&page_pool->lock);
            deactivate_payload_page(page_pool, page);
            MONAD_SPINLOCK_UNLOCK(&page_pool->lock);
        }
    }
}

void _monad_event_recorder_init_thread_cache(
    struct monad_event_recorder_thr *thread_cache)
{
    struct monad_event_descriptor *event;
    struct monad_event_thread_info local_thread_info;
    struct monad_event_thread_info *thread_info;
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;
    unsigned s;

    memset(thread_cache, 0, sizeof *thread_cache);
    memset(&local_thread_info, 0, sizeof local_thread_info);
    local_thread_info.epoch_nanos = monad_event_get_epoch_nanos();
    local_thread_info.process_id = rss->process_id;
    local_thread_info.thread_id = thread_cache->thread_id =
        (uint64_t)get_tl_tid();
    (void)pthread_getname_np(
        pthread_self(),
        local_thread_info.thread_name,
        sizeof local_thread_info.thread_name);

    // Reserve a source_id for this thread recorder, add it to the global list
    MONAD_SPINLOCK_LOCK(&rss->lock);
    // TOOD(ken): this gives us a maximum of 64 recording threads, but we have
    // enough bits in the event descriptor to support 256 threads
    s = stdc_first_trailing_zero(rss->thread_source_ids);
    MONAD_ASSERT_PRINTF(
        s > 0,
        "no space left in source_id bitmap for new thread %s:%lu",
        local_thread_info.thread_name,
        local_thread_info.thread_id);
    local_thread_info.source_id = thread_cache->source_id = (uint8_t)s;
    rss->thread_source_ids |= 1UL << (s - 1);

    // Copy local thread info into the metadata array that's present in shared
    // memory
    thread_info = &rss->thread_info_table[s];
    memcpy(thread_info, &local_thread_info, sizeof local_thread_info);
    TAILQ_INSERT_TAIL(&rss->thread_caches, thread_cache, next);
    pthread_setspecific(rss->thread_cache_key, thread_cache);
    MONAD_SPINLOCK_UNLOCK(&rss->lock);

    // Announce the creation of this thread
    event = _monad_event_ring_reserve_descriptor(
        &g_monad_event_recorders[MONAD_EVENT_RING_EXEC].event_ring,
        &thread_info->seqno);
    event->type = MONAD_EVENT_THREAD_CREATE;
    event->epoch_nanos = thread_info->epoch_nanos;
    event->pop_scope = 0;
    event->source_id = thread_info->source_id;
    set_metadata_descriptor_payload(thread_info, sizeof *thread_info, event);
    atomic_store_explicit(
        &event->seqno, thread_info->seqno, memory_order_release);
}

int monad_event_recorder_export_metadata_section(
    enum monad_event_metadata_type type, uint16_t *page_id, uint32_t *offset)
{
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;

    MONAD_ASSERT(page_id != nullptr && offset != nullptr);
    *page_id = rss->metadata_page->page_id;
    switch (type) {
    case MONAD_EVENT_METADATA_THREAD:
        *offset = (uint32_t)((uint8_t *)rss->thread_info_table -
                             (uint8_t *)rss->metadata_page);
        return 0;

    case MONAD_EVENT_METADATA_BLOCK_FLOW:
        *offset = (uint32_t)((uint8_t *)rss->block_header_table -
                             (uint8_t *)rss->metadata_page);
        return 0;

    default:
        return FORMAT_ERRC(EINVAL, "unknown metadata type: %hhu", type);
    }
}

int monad_event_init_local_iterator(
    enum monad_event_ring_type ring_type, struct monad_event_iterator *iter,
    size_t *payload_page_count)
{
    struct monad_event_recorder *recorder;

    MONAD_ASSERT(iter != nullptr);
    if (ring_type >= MONAD_EVENT_RING_COUNT) {
        return FORMAT_ERRC(EINVAL, "invalid ring type %hhu", ring_type);
    }
    recorder = &g_monad_event_recorders[ring_type];
    if (!atomic_load_explicit(&recorder->enabled, memory_order_acquire)) {
        return FORMAT_ERRC(
            ENODEV, "event recorder %hhu not enabled", ring_type);
    }
    iter->desc_table = recorder->event_ring.descriptor_table;
    iter->payload_pages =
        (struct monad_event_payload_page const **)recorder->all_pages;
    iter->capacity_mask = recorder->event_ring.capacity_mask;
    iter->write_last_seqno = &recorder->event_ring.control->last_seqno;
    if (payload_page_count != nullptr) {
        *payload_page_count = recorder->all_pages_size;
    }
    return 0;
}

__attribute__((weak)) uint32_t monad_event_get_txn_num()
{
    return 0;
}
