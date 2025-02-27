#include <errno.h>
#include <stdarg.h>
#include <stdbit.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <pthread.h>
#include <unistd.h>

#include <fcntl.h>
#include <sys/file.h>
#include <sys/mman.h>
#include <sys/queue.h>
#include <sys/types.h>

#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/event/event.h>
#include <monad/event/event_error.h>
#include <monad/event/event_recorder.h>

static thread_local char g_error_buf[1024];
static size_t const PAGE_2MB = 1UL << 21;

__attribute__((format(printf, 3, 4))) static int format_errc(
    struct monad_event_source_location const *srcloc, int err,
    char const *format, ...)
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
    format_errc(&MONAD_EVENT_SOURCE_LOCATION_CURRENT(), __VA_ARGS__)

// Reuse an internal function from event.c
extern int _monad_event_ring_mmap_data(
    struct monad_event_ring *, int ring_fd, char const *error_name);

/*
 * Event ring setup functions
 */

// Try to open the event ring file and place an exclusive lock on it
static int open_event_ring_file(char const *file_path, int *ring_fd)
{
    mode_t const create_mode = S_IRUSR | S_IRGRP | S_IWUSR | S_IWGRP | S_IROTH;
    int rc;

    // Open the event ring file; we're not using O_EXCL or O_TRUNC, so we may
    // open an event ring file that is actively used by another process, or a
    // zombie one from a dead process
    *ring_fd = open(file_path, O_RDWR | O_CREAT, create_mode);
    if (*ring_fd == -1) {
        return FORMAT_ERRC(errno, "open of event ring `%s` failed", file_path);
    }

    // Try to place a BSD-style exclusive lock on the event ring; if this
    // succeeds, we're the new owner, otherwise `file_path` is taken
    rc = flock(*ring_fd, LOCK_EX | LOCK_NB);
    if (rc == -1) {
        rc = FORMAT_ERRC(rc, "flock of event ring `%s` failed", file_path);
        goto Error;
    }
    return 0;

Error:
    (void)close(*ring_fd);
    if (rc == EWOULDBLOCK) {
        // Someone else owns this; explicitly clear ring_fd so that later
        // cleanup logic will know it's not ours, and won't try to unlink(2)
        // its name from the files system
        *ring_fd = -1;
    }
    return rc;
}

// Given a description of the memory resources needed for an event ring,
// "allocate" that memory and set up the ring. This will ftruncate(2) the event
// ring file to the appropriate size, mmap the first page, and fill out the
// header structure
static int init_event_ring_file(
    struct monad_event_recorder_config const *ring_config, int ring_fd,
    struct monad_event_ring_header **header_p)
{
    struct monad_event_ring_header *header;
    char memfd_name[24];
    size_t ring_data_size;

    if (ftruncate(ring_fd, (off_t)PAGE_2MB) == -1) {
        return FORMAT_ERRC(
            errno,
            "ftruncate of event ring `%s` to header size failed",
            ring_config->file_path);
    }
    *header_p = header =
        mmap(nullptr, PAGE_2MB, PROT_WRITE, MAP_SHARED, ring_fd, 0);
    if (header == MAP_FAILED) {
        return FORMAT_ERRC(
            errno,
            "mmap of event ring `%s` header page failed",
            ring_config->file_path);
    }
    header->ring_capacity = 1UL << ring_config->ring_shift;
    header->payload_buf_size = 1UL << ring_config->payload_buf_shift;
    memset(&header->control, 0, sizeof header->control);

    // Until we have hugetlbfs, this file is just a discovery mechanism that
    // allows us to find the "real" ring data file, which is a memfd_create(2)
    // file
    header->is_discovery = true;
    snprintf(memfd_name, sizeof memfd_name, "eringdata-%d", ring_fd);
    header->data_fd = memfd_create(memfd_name, MFD_CLOEXEC | MFD_HUGETLB);
    if (header->data_fd == -1) {
        return FORMAT_ERRC(
            errno,
            "memfd_create of ring_data_fd for event ring `%s` failed",
            ring_config->file_path);
    }
    ring_data_size =
        header->ring_capacity * sizeof(struct monad_event_descriptor) +
        header->payload_buf_size;
    if (ftruncate(header->data_fd, (off_t)ring_data_size) == -1) {
        return FORMAT_ERRC(
            errno,
            "ftruncate of ring_data_fd for event ring `%s` failed",
            ring_config->file_path);
    }

    return 0;
}

/*
 * Event recorder functions
 */

struct monad_event_recorder_shared_state g_monad_event_recorder_shared_state;

// Initialization of the event recording system that happens prior to the
// process' `main` function being called. This makes the API-level init call
// implementation simpler, as we can rely on some data structures already being
// initialized.
static void __attribute__((constructor(MONAD_EVENT_RECORDER_CTOR_PRIO)))
event_system_ctor()
{
    int rc;
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;

    rc = pthread_mutex_init(&rss->mtx, nullptr);
    MONAD_ASSERT_PRINTF(
        rc == 0, "unable to init recorder shared state mutex, error: %d", rc);
    TAILQ_INIT(&rss->recorders);
}

// Cleanup routine that runs automatically after `main` returns or libc
// exit(3) is called; destroys all the recorders and frees the resources taken
// in the above constructor
static void __attribute__((destructor(MONAD_EVENT_RECORDER_CTOR_PRIO)))
event_system_dtor()
{
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;
    struct monad_event_recorder *recorder;

    while ((recorder = TAILQ_FIRST(&rss->recorders)) != nullptr) {
        monad_event_recorder_destroy(recorder);
    }
    pthread_mutex_destroy(&rss->mtx);
}

int monad_event_recorder_create(
    struct monad_event_recorder **recorder_p,
    struct monad_event_recorder_config const *ring_config)
{
    int rc;
    struct monad_event_recorder *recorder;
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;

    if (recorder_p == nullptr) {
        return FORMAT_ERRC(EFAULT, "recorder_p cannot be nullptr");
    }
    *recorder_p = nullptr;
    if (ring_config == nullptr) {
        return FORMAT_ERRC(EFAULT, "ring_config cannot be nullptr");
    }
    if (ring_config->file_path == nullptr) {
        return FORMAT_ERRC(EFAULT, "ring_config file_path cannot be nullptr");
    }
    if (ring_config->ring_shift < MONAD_EVENT_MIN_RING_SHIFT ||
        ring_config->ring_shift > MONAD_EVENT_MAX_RING_SHIFT) {
        return FORMAT_ERRC(
            ERANGE,
            "ring_shift outside allowed range [%hhu, %hhu]: "
            "(ring sizes: [%lu, %lu])",
            MONAD_EVENT_MIN_RING_SHIFT,
            MONAD_EVENT_MAX_RING_SHIFT,
            (1UL << MONAD_EVENT_MIN_RING_SHIFT),
            (1UL << MONAD_EVENT_MAX_RING_SHIFT));
    }
    if (ring_config->payload_buf_shift < MONAD_EVENT_MIN_PAYLOAD_BUF_SHIFT ||
        ring_config->payload_buf_shift > MONAD_EVENT_MAX_PAYLOAD_BUF_SHIFT) {
        return FORMAT_ERRC(
            ERANGE,
            "payload_buf_shift outside allowed range [%hhu, %hhu]: "
            "(buffer sizes: [%lu, %lu])",
            MONAD_EVENT_MIN_PAYLOAD_BUF_SHIFT,
            MONAD_EVENT_MAX_PAYLOAD_BUF_SHIFT,
            (1UL << MONAD_EVENT_MIN_PAYLOAD_BUF_SHIFT),
            (1UL << MONAD_EVENT_MAX_PAYLOAD_BUF_SHIFT));
    }

    rc = posix_memalign((void **)recorder_p, 64, sizeof *recorder);
    if (rc != 0) {
        return FORMAT_ERRC(
            rc, "posix_memalign for monad_event_recorder failed");
    }
    recorder = *recorder_p;
    memset(recorder, 0, sizeof *recorder);
    recorder->ring_fd = -1;
    recorder->file_path = strdup(ring_config->file_path);
    if (recorder->file_path == nullptr) {
        rc = FORMAT_ERRC(
            errno, "strdup failed for file_path `%s`", ring_config->file_path);
        goto Error;
    }

    // Open the event ring file, initialize it, and map the event ring into
    // our address space
    rc = open_event_ring_file(ring_config->file_path, &recorder->ring_fd);
    if (rc != 0) {
        goto Error;
    }
    rc = init_event_ring_file(
        ring_config, recorder->ring_fd, &recorder->event_ring.header);
    if (rc != 0) {
        goto Error;
    }
    rc = _monad_event_ring_mmap_data(
        &recorder->event_ring, recorder->ring_fd, recorder->file_path);
    if (rc != 0) {
        strlcpy(
            g_error_buf, monad_event_ring_get_last_error(), sizeof g_error_buf);
        goto Error;
    }

    // These fields are all canonically defined in the header section of the
    // shared memory file; we place them all on the same cache line in the
    // recorder, for the sake of hot path performance
    recorder->control = &recorder->event_ring.header->control;
    recorder->capacity_mask = recorder->event_ring.header->ring_capacity - 1;
    recorder->payload_buf_mask =
        recorder->event_ring.header->payload_buf_size - 1;

    // Add the recorder to the global list
    pthread_mutex_lock(&rss->mtx);
    TAILQ_INSERT_TAIL(&rss->recorders, recorder, next);
    pthread_mutex_unlock(&rss->mtx);

    return 0;

Error:
    if (recorder->ring_fd != -1) {
        // This implies we took the lock; explicitly unlock it (in case other
        // fd's to this file are open) and unlink its name from the file system
        unlink(recorder->file_path);
        (void)flock(recorder->ring_fd, LOCK_UN);
        close(recorder->ring_fd);
    }
    free((void *)recorder->file_path);
    free(recorder);
    *recorder_p = nullptr;
    return rc;
}

void monad_event_recorder_destroy(struct monad_event_recorder *recorder)
{
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;

    if (recorder == nullptr) {
        return;
    }
    pthread_mutex_lock(&rss->mtx);
    TAILQ_REMOVE(&rss->recorders, recorder, next);
    pthread_mutex_unlock(&rss->mtx);
    (void)close(recorder->ring_fd);
    if (recorder->event_ring.header != nullptr) {
        (void)close(recorder->event_ring.header->data_fd);
    }
    monad_event_ring_unmap(&recorder->event_ring);
    unlink(recorder->file_path);
    free((void *)recorder->file_path);
    free(recorder);
}

char const *monad_event_recorder_get_last_error()
{
    return g_error_buf;
}
