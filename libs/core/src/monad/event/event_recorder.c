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
#include <monad/core/likely.h>
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

static void cleanup_event_ring(
    struct monad_event_ring *ring, struct monad_event_ring_fds *fds)
{
    size_t const desc_table_map_len =
        ring->capacity * sizeof(struct monad_event_descriptor);
    if (ring->control != nullptr) {
        munmap(ring->control, (size_t)getpagesize());
        (void)close(fds->control_fd);
        fds->control_fd = -1;
    }
    if (ring->descriptors != nullptr) {
        munmap(ring->descriptors, desc_table_map_len);
        (void)close(fds->descriptor_array_fd);
        fds->descriptor_array_fd = -1;
    }
    if (ring->payload_buf != nullptr) {
        munmap(
            ring->payload_buf,
            ring->payload_buf_size + MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE);
        (void)close(fds->payload_buf_fd);
        fds->payload_buf_fd = -1;
    }
}

static int init_event_ring(
    struct monad_event_ring *ring, enum monad_event_ring_type ring_type,
    uint8_t ring_shift, uint8_t payload_buf_shift,
    struct monad_event_ring_fds *fds)
{
    size_t mmap_page_size;
    size_t desc_table_map_len;
    int saved_error;
    char name[32];

    memset(ring, 0, sizeof *ring);
    fds->control_fd = -1;
    fds->descriptor_array_fd = -1;
    fds->payload_buf_fd = -1;

    // Map the ring control structure (a single, minimum-sized VM page)
    mmap_page_size = (size_t)getpagesize();
    snprintf(name, sizeof name, "evt_rc:%d:%hhu", getpid(), ring_type);
    fds->control_fd = memfd_create(name, MFD_CLOEXEC);
    if (fds->control_fd == -1) {
        saved_error = FORMAT_ERRC(errno, "memfd_create(2) failed for %s", name);
        goto Error;
    }
    if (ftruncate(fds->control_fd, (off_t)mmap_page_size) == -1) {
        saved_error = FORMAT_ERRC(errno, "ftruncate(2) failed for %s", name);
        goto Error;
    }
    ring->control = mmap(
        nullptr,
        mmap_page_size,
        PROT_READ | PROT_WRITE,
        MAP_SHARED,
        fds->control_fd,
        0);
    if (ring->control == MAP_FAILED) {
        saved_error = FORMAT_ERRC(errno, "mmap(2) unable to map %s", name);
        goto Error;
    }

    // Map the ring descriptor array
    ring->capacity = 1UL << ring_shift;
    MONAD_ASSERT(stdc_has_single_bit(ring->capacity));
    desc_table_map_len = ring->capacity * sizeof(struct monad_event_descriptor);
    snprintf(name, sizeof name, "evt_rdt:%d:%hhu", getpid(), ring_type);
    fds->descriptor_array_fd = memfd_create(name, MFD_CLOEXEC | MFD_HUGETLB);
    if (fds->descriptor_array_fd == -1) {
        saved_error = FORMAT_ERRC(errno, "memfd_create(2) failed for %s", name);
        goto Error;
    }
    if (ftruncate(fds->descriptor_array_fd, (off_t)desc_table_map_len) == -1) {
        saved_error = FORMAT_ERRC(errno, "ftruncate(2) failed for %s", name);
        goto Error;
    }
    ring->descriptors = mmap(
        nullptr,
        desc_table_map_len,
        PROT_READ | PROT_WRITE,
        MAP_SHARED | MAP_HUGETLB | MAP_POPULATE,
        fds->descriptor_array_fd,
        0);
    if (ring->descriptors == MAP_FAILED) {
        saved_error = FORMAT_ERRC(errno, "mmap(2) unable to map %s", name);
        goto Error;
    }

    // Map the payload buffer
    ring->payload_buf_size = 1UL << payload_buf_shift;
    MONAD_ASSERT(stdc_has_single_bit(ring->payload_buf_size));
    snprintf(name, sizeof name, "evt_pbuf:%d:%hhu", getpid(), ring_type);
    fds->payload_buf_fd = memfd_create(name, MFD_CLOEXEC | MFD_HUGETLB);
    if (fds->payload_buf_fd == -1) {
        saved_error = FORMAT_ERRC(errno, "memfd_create(2) failed for %s", name);
        goto Error;
    }
    if (ftruncate(fds->payload_buf_fd, (off_t)ring->payload_buf_size) == -1) {
        saved_error = FORMAT_ERRC(errno, "ftruncate(2) failed for %s", name);
        goto Error;
    }

    // First, reserve a single anonymous mapping whose size encompasses both
    // the nominal size of the payload buffer plus the size of the wrap-around
    // large pages. We'll remap the memfd into this reserved range later, using
    // MAP_FIXED.
    ring->payload_buf = mmap(
        nullptr,
        ring->payload_buf_size + MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE,
        PROT_READ | PROT_WRITE,
        MAP_SHARED | MAP_ANONYMOUS | MAP_HUGETLB,
        -1,
        0);
    if (ring->payload_buf == MAP_FAILED) {
        saved_error = FORMAT_ERRC(errno, "mmap(2) unable to map %s", name);
        goto Error;
    }

    // Map the payload buffer into the first part of the space we just reserved
    if (mmap(
            ring->payload_buf,
            ring->payload_buf_size,
            PROT_READ | PROT_WRITE,
            MAP_SHARED | MAP_FIXED | MAP_HUGETLB | MAP_POPULATE,
            fds->payload_buf_fd,
            0) == MAP_FAILED) {
        saved_error = FORMAT_ERRC(
            errno,
            "unable to remap payload buffer range to memfd for %s",
            name);
        goto Error;
    }

    // Map the "wrap around" large pages after the payload buffer. This causes
    // the first large pages of the buffer (enough to hold a full event payload
    // of maximum size) to be mapped immediately after the end of the buffer,
    // allowing us to naturally "wrap around" in memory by the size of one
    // maximally-sized event. Thus we can memcpy(3) event payloads safely near
    // the end of the buffer, and it will wrap around in memory without needing
    // to do any error-prone index massaging.
    if (mmap(
            (uint8_t *)ring->payload_buf_size +
                MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE,
            MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE,
            PROT_READ | PROT_WRITE,
            MAP_SHARED | MAP_FIXED | MAP_HUGETLB | MAP_POPULATE,
            fds->payload_buf_fd,
            0) == MAP_FAILED) {
        saved_error = FORMAT_ERRC(
            errno, "mmap(2) wrap-around mapping for %s failed", name);
        goto Error;
    }
    return 0;

Error:
    cleanup_event_ring(ring, fds);
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
        recorder->event_ring_fds.control_fd =
            recorder->event_ring_fds.descriptor_array_fd =
                recorder->event_ring_fds.payload_buf_fd = -1;
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
        cleanup_event_ring(&recorder->event_ring, &recorder->event_ring_fds);
    }
    pthread_key_delete(rss->thread_cache_key);
}

struct ring_size_params
{
    uint8_t default_ring_shift;
    uint8_t min_ring_shift;
    uint8_t max_ring_shift;
    uint8_t default_payload_buf_shift;
    uint8_t min_payload_buf_shift;
    uint8_t max_payload_buf_shift;
} s_ring_size_params[] = {
    [MONAD_EVENT_RING_EXEC] =
        {.default_ring_shift = MONAD_EVENT_DEFAULT_EXEC_RING_SHIFT,
         .min_ring_shift = MONAD_EVENT_MIN_EXEC_RING_SHIFT,
         .max_ring_shift = MONAD_EVENT_MAX_EXEC_RING_SHIFT,
         .default_payload_buf_shift =
             MONAD_EVENT_DEFAULT_EXEC_PAYLOAD_BUF_SHIFT,
         .min_payload_buf_shift = MONAD_EVENT_MIN_EXEC_PAYLOAD_BUF_SHIFT,
         .max_payload_buf_shift = MONAD_EVENT_MAX_EXEC_PAYLOAD_BUF_SHIFT},
    /* TODO(ken): to be figured out later */
    [MONAD_EVENT_RING_TRACE] =
        {.default_ring_shift = MONAD_EVENT_DEFAULT_EXEC_RING_SHIFT,
         .min_ring_shift = MONAD_EVENT_MIN_EXEC_RING_SHIFT,
         .max_ring_shift = MONAD_EVENT_MAX_EXEC_RING_SHIFT,
         .default_payload_buf_shift =
             MONAD_EVENT_DEFAULT_EXEC_PAYLOAD_BUF_SHIFT,
         .min_payload_buf_shift = MONAD_EVENT_MIN_EXEC_PAYLOAD_BUF_SHIFT,
         .max_payload_buf_shift = MONAD_EVENT_MAX_EXEC_PAYLOAD_BUF_SHIFT},
};

static int configure_recorder_locked(
    struct monad_event_recorder *recorder, uint8_t ring_shift,
    uint8_t payload_buf_shift)
{
    MONAD_DEBUG_ASSERT(monad_spinlock_is_self_owned(&recorder->lock));
    if (atomic_load_explicit(&recorder->enabled, memory_order_acquire)) {
        return FORMAT_ERRC(
            EBUSY, "event recorder already running; cannot configure");
    }
    if (recorder->event_ring.control != nullptr) {
        // Reconfiguring; tear everything down and do it again
        cleanup_event_ring(&recorder->event_ring, &recorder->event_ring_fds);
    }
    if (ring_shift == 0) {
        ring_shift = s_ring_size_params[recorder->ring_type].default_ring_shift;
    }
    return init_event_ring(
        &recorder->event_ring,
        recorder->ring_type,
        ring_shift,
        payload_buf_shift,
        &recorder->event_ring_fds);
}

int monad_event_recorder_configure(
    enum monad_event_ring_type ring_type, uint8_t ring_shift,
    uint8_t payload_buf_shift)
{
    int rc;
    struct monad_event_recorder *recorder;
    struct ring_size_params const *rsp;

    if (ring_type >= MONAD_EVENT_RING_COUNT) {
        return FORMAT_ERRC(
            EINVAL, "ring_type %hhu is not a valid value", ring_type);
    }
    rsp = &s_ring_size_params[ring_type];
    if (ring_shift < rsp->min_ring_shift || ring_shift > rsp->max_ring_shift) {
        return FORMAT_ERRC(
            ERANGE,
            "%hhu ring_shift outside allowed range [%hhu, %hhu]: "
            "(ring sizes: [%lu, %lu])",
            ring_type,
            rsp->min_ring_shift,
            rsp->max_ring_shift,
            (1UL << rsp->min_ring_shift),
            (1UL << rsp->max_ring_shift));
    }
    if (payload_buf_shift < rsp->min_payload_buf_shift ||
        payload_buf_shift > rsp->max_payload_buf_shift) {
        return FORMAT_ERRC(
            ERANGE,
            "%hhu payload_buf_shift outside allowed range [%hhu, %hhu]: "
            "(buffer sizes: [%lu, %lu])",
            ring_type,
            rsp->min_payload_buf_shift,
            rsp->max_payload_buf_shift,
            (1UL << rsp->min_payload_buf_shift),
            (1UL << rsp->max_payload_buf_shift));
    }

    recorder = &g_monad_event_recorders[ring_type];
    MONAD_SPINLOCK_LOCK(&recorder->lock);
    rc = configure_recorder_locked(recorder, ring_shift, payload_buf_shift);
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
        rc = configure_recorder_locked(
            recorder,
            s_ring_size_params[recorder->ring_type].default_ring_shift,
            s_ring_size_params[recorder->ring_type].default_payload_buf_shift);
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
    iter->descriptors = recorder->event_ring.descriptors;
    iter->capacity_mask = recorder->event_ring.capacity - 1;
    iter->payload_buf = recorder->event_ring.payload_buf;
    iter->payload_buf_size = recorder->event_ring.payload_buf_size;
    iter->write_last_seqno = &recorder->event_ring.control->last_seqno;
    iter->buffer_window_start =
        &recorder->event_ring.control->buffer_window_start;
    iter->read_last_seqno =
        __atomic_load_n(iter->write_last_seqno, __ATOMIC_ACQUIRE);
    return 0;
}

__attribute__((weak)) uint32_t monad_event_get_txn_id()
{
    return 0;
}
