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
#include <monad/event/event_iterator.h>
#include <monad/event/event_protocol.h>
#include <monad/event/event_recorder.h>
#include <monad/event/event_shared.h>

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
 * Metadata page functions
 */

static int
mmap_metadata_page(struct monad_event_metadata_page *page, size_t size)
{
    char name[32];

    snprintf(name, sizeof name, "er_meta_%d", getpid());
    page->map_len = size;
    page->memfd = memfd_create(name, MFD_CLOEXEC | MFD_HUGETLB);
    if (page->memfd == -1) {
        return FORMAT_ERRC(errno, "memfd_create(2) failed for %s", name);
    }
    if (ftruncate(page->memfd, (off_t)page->map_len) == -1) {
        return FORMAT_ERRC(errno, "ftruncate(2) failed for %s", name);
    }
    page->base_addr = mmap(
        nullptr,
        page->map_len,
        PROT_WRITE,
        MAP_SHARED | MAP_HUGETLB | MAP_POPULATE,
        page->memfd,
        0);
    if (page->base_addr == MAP_FAILED) {
        return FORMAT_ERRC(errno, "mmap(2) unable to map %s", name);
    }

    page->heap_next = page->heap_begin = page->base_addr;
    page->heap_end = page->heap_begin + size;
    return 0;
}

static void *alloc_from_metadata_page(
    struct monad_event_metadata_page *page, size_t payload_size,
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
    return payload;
}

/*
 * Event ring functions
 */

void cleanup_event_ring(
    struct monad_event_ring *ring, int *control_fd, int *fifo_fd)
{
    if (ring->control != nullptr) {
        munmap(ring->control, (size_t)getpagesize());
        (void)close(*control_fd);
        *control_fd = -1;
        ring->control = nullptr;
    }
    if (ring->fifo_buf != nullptr) {
        munmap(
            ring->fifo_buf, ring->fifo_size + MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE);
        (void)close(*fifo_fd);
        *fifo_fd = -1;
        ring->fifo_buf = nullptr;
    }
}

int init_event_ring(
    struct monad_event_ring *ring, enum monad_event_ring_type ring_type,
    uint8_t ring_shift, int *control_fd, int *fifo_fd)
{
    size_t mmap_page_size;
    int saved_error;
    char name[32];

    memset(ring, 0, sizeof *ring);
    *control_fd = -1;
    *fifo_fd = -1;

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

    // Map the FIFO buffer; this uses huge pages and also the "wrap-around"
    // technique.
    ring->fifo_size = 1UL << ring_shift;
    MONAD_ASSERT(
        stdc_has_single_bit(ring->fifo_size) &&
        ring->fifo_size > MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE * 2);
    snprintf(name, sizeof name, "evt_rfifo:%d:%hhu", getpid(), ring_type);
    *fifo_fd = memfd_create(name, MFD_CLOEXEC | MFD_HUGETLB);
    if (*fifo_fd == -1) {
        saved_error = FORMAT_ERRC(errno, "memfd_create(2) failed for %s", name);
        goto Error;
    }
    if (ftruncate(*fifo_fd, (off_t)ring->fifo_size) == -1) {
        saved_error = FORMAT_ERRC(errno, "ftruncate(2) failed for %s", name);
        goto Error;
    }

    // First, reserve a single anonymous mapping whose size encompasses both
    // the nominal size of the FIFO buffer plus the size of the wrap-around
    // large pages. We'll remap the memfd into this reserved range later,
    // using MAP_FIXED.
    ring->fifo_buf = mmap(
        nullptr,
        ring->fifo_size + MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE,
        PROT_READ | PROT_WRITE,
        MAP_SHARED | MAP_ANONYMOUS | MAP_HUGETLB,
        -1,
        0);
    if (ring->fifo_buf == MAP_FAILED) {
        saved_error = FORMAT_ERRC(errno, "mmap(2) unable to map %s", name);
        goto Error;
    }

    // Map the FIFO buffer into the first part of the space we just reserved
    if (mmap(
            ring->fifo_buf,
            ring->fifo_size,
            PROT_READ | PROT_WRITE,
            MAP_SHARED | MAP_FIXED | MAP_HUGETLB | MAP_POPULATE,
            *fifo_fd,
            0) == MAP_FAILED) {
        saved_error = FORMAT_ERRC(
            errno,
            "unable to remap descriptor table range to memfd for %s",
            name);
        goto Error;
    }

    // Map the "wrap around" large pages after the FIFO buffer. This causes
    // the first large pages of the buffer to be mapped immediately after the
    // end of the buffer, allowing us to naturally "wrap around" in memory by
    // the size of the maximum event payload. Thus we can bulk memcpy(3) event
    // payloads safely near the end of the buffer, and it will wrap around
    // in memory without doing any error-prone index massaging.
    if (mmap(
            (uint8_t *)ring->fifo_buf + ring->fifo_size,
            MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE,
            PROT_READ | PROT_WRITE,
            MAP_SHARED | MAP_FIXED | MAP_HUGETLB | MAP_POPULATE,
            *fifo_fd,
            0) == MAP_FAILED) {
        saved_error = FORMAT_ERRC(
            errno, "mmap(2) wrap-around mapping for %s failed", name);
        goto Error;
    }

    // Despite the MAP_POPULATE, we don't necessarily trust that everything
    // is ready yet; "warm up" the mappings by zeroing out the entire range
    memset(
        ring->fifo_buf, 0, ring->fifo_size + MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE);
    return 0;

Error:
    cleanup_event_ring(ring, control_fd, fifo_fd);
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
    struct monad_event_metadata_page *const metadata_page = &rss->metadata_page;

    monad_spinlock_init(&rss->lock);
    TAILQ_INIT(&rss->thread_caches);
    rc = pthread_key_create(&rss->thread_cache_key, thread_cache_dtor);
    MONAD_ASSERT_PRINTF(
        rc == 0, "unable to create thread recorder pthread key, error: %d", rc);

    snprintf(name, sizeof name, "epp_meta_%d", getpid());
    // Allocate a special page to hold fixed metadata, which is shared by
    // all recorders and never recycled
    rc = mmap_metadata_page(metadata_page, PAGE_2MB);
    MONAD_ASSERT_PRINTF(rc == 0, "unable to mmap metadata page, error: %d", rc);
    metadata_page->thread_info_table = alloc_from_metadata_page(
        metadata_page,
        (UINT8_MAX + 1) * sizeof metadata_page->thread_info_table[0],
        nullptr);
    MONAD_ASSERT(metadata_page->thread_info_table != nullptr);
    metadata_page->block_header_table = alloc_from_metadata_page(
        metadata_page,
        (1U << 12) * sizeof metadata_page->thread_info_table[0],
        nullptr);
    MONAD_ASSERT(metadata_page->block_header_table != nullptr);
    rss->process_id = (uint64_t)getpid();

    for (uint8_t q = 0; q < MONAD_EVENT_RING_COUNT; ++q) {
        recorder = &g_monad_event_recorders[q];
        memset(recorder, 0, sizeof *recorder);
        monad_spinlock_init(&recorder->lock);
        recorder->ring_type = q;
        recorder->control_fd = recorder->fifo_fd = -1;
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
            &recorder->event_ring, &recorder->control_fd, &recorder->fifo_fd);
    }
    pthread_key_delete(rss->thread_cache_key);
}

static int configure_recorder_locked(
    struct monad_event_recorder *recorder, uint8_t ring_shift)
{
    int rc;

    MONAD_DEBUG_ASSERT(monad_spinlock_is_self_owned(&recorder->lock));
    if (atomic_load_explicit(&recorder->enabled, memory_order_acquire)) {
        return FORMAT_ERRC(
            EBUSY, "event recorder already running; cannot configure");
    }
    if (recorder->event_ring.control != nullptr) {
        // Reconfiguring; tear everything down and do it again
        cleanup_event_ring(
            &recorder->event_ring, &recorder->control_fd, &recorder->fifo_fd);
    }
    if (ring_shift == 0) {
        ring_shift = MONAD_EVENT_DEFAULT_RING_SHIFT;
    }
    if ((rc = init_event_ring(
             &recorder->event_ring,
             recorder->ring_type,
             ring_shift,
             &recorder->control_fd,
             &recorder->fifo_fd)) != 0) {
        return rc;
    }
    recorder->next_seqno = 1;
    return 0;
}

int monad_event_recorder_configure(
    enum monad_event_ring_type ring_type, uint8_t ring_shift)
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
            "ring_shift out allowed range [%hhu, %hhu]: "
            "(ring sizes: [%lu, %lu])",
            MONAD_EVENT_MIN_RING_SHIFT,
            MONAD_EVENT_MAX_RING_SHIFT,
            (1UL << MONAD_EVENT_MIN_RING_SHIFT),
            (1UL << MONAD_EVENT_MAX_RING_SHIFT));
    }

    recorder = &g_monad_event_recorders[ring_type];
    MONAD_SPINLOCK_LOCK(&recorder->lock);
    rc = configure_recorder_locked(recorder, ring_shift);
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
    if (recorder->event_ring.control == nullptr) {
        rc =
            configure_recorder_locked(recorder, MONAD_EVENT_DEFAULT_RING_SHIFT);
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
}

void _monad_event_recorder_init_thread_cache(
    struct monad_event_recorder_thr *thread_cache)
{
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
    thread_info = &rss->metadata_page.thread_info_table[s];
    memcpy(thread_info, &local_thread_info, sizeof local_thread_info);
    TAILQ_INSERT_TAIL(&rss->thread_caches, thread_cache, next);
    pthread_setspecific(rss->thread_cache_key, thread_cache);
    MONAD_SPINLOCK_UNLOCK(&rss->lock);

    // Announce the creation of this thread
    MONAD_EVENT_EXPR(MONAD_EVENT_THREAD_CREATE, 0, *thread_info);
}

int monad_event_recorder_export_metadata_section(
    enum monad_event_metadata_type type, uint32_t *offset)
{
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;

    MONAD_ASSERT(offset != nullptr);
    switch (type) {
    case MONAD_EVENT_METADATA_THREAD:
        *offset = (uint32_t)((uint8_t *)rss->metadata_page.thread_info_table -
                             (uint8_t *)rss->metadata_page.base_addr);
        return 0;

    case MONAD_EVENT_METADATA_BLOCK_FLOW:
        *offset = (uint32_t)((uint8_t *)rss->metadata_page.block_header_table -
                             (uint8_t *)rss->metadata_page.base_addr);
        return 0;

    default:
        return FORMAT_ERRC(EINVAL, "unknown metadata type: %hhu", type);
    }
}

int monad_event_init_local_iterator(
    enum monad_event_ring_type ring_type, struct monad_event_iterator *iter)
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
    memset(iter, 0, sizeof *iter);
    iter->fifo_buf = recorder->event_ring.fifo_buf;
    iter->fifo_size = recorder->event_ring.fifo_size;
    iter->ring_next_byte = &recorder->event_ring.control->next_byte;
    iter->ring_last_event_range =
        &recorder->event_ring.control->last_event_range;
    return 0;
}

__attribute__((weak)) uint32_t monad_event_get_txn_num()
{
    return 0;
}
