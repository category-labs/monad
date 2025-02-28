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
#include <sys/mman.h>
#include <sys/queue.h>
#include <sys/types.h>

#include <monad/core/assert.h>
#include <monad/core/format_err.h>
#include <monad/core/likely.h>
#include <monad/event/event.h>
#include <monad/event/event_recorder.h>

extern thread_local char _g_monad_event_error_buf[1024]; // Defined in event.c
static size_t const PAGE_2MB = 1UL << 21, HEADER_SIZE = PAGE_2MB;

#define FORMAT_ERRC(...)                                                       \
    monad_format_err(                                                          \
        _g_monad_event_error_buf,                                              \
        sizeof(_g_monad_event_error_buf),                                      \
        &MONAD_SOURCE_LOCATION_CURRENT(),                                      \
        __VA_ARGS__)

// Reuse an internal function from event.c
extern int _monad_event_ring_mmap_data(
    struct monad_event_ring *, int ring_fd, off_t ring_offset,
    char const *error_name);

/*
 * Event ring setup functions
 */

// Try to open the event ring file and place an exclusive lock on the range
// that will hold the event ring data
static int open_event_ring_file(
    struct monad_event_recorder *recorder, int open_flags, mode_t mode)
{
    struct flock lock = {
        .l_type = F_WRLCK,
        .l_whence = SEEK_SET,
        .l_start = recorder->ring_file_offset,
        .l_len = (off_t)recorder->total_ring_bytes,
        .l_pid = 0,
    };

    // Open the event ring file; this may open a file that is actively used by
    // another process, or a zombie one from a dead process
    recorder->ring_fd = open(recorder->file_path, O_RDWR | open_flags, mode);
    if (recorder->ring_fd == -1) {
        return FORMAT_ERRC(
            errno,
            "open of event ring `%s` with flags=%d, mode=%d failed",
            recorder->file_path,
            open_flags,
            mode);
    }

    // Try to place an OFD range lock on the event ring; if this succeeds,
    // we're the new owner, otherwise this range of `file_path` is taken
    if (fcntl(recorder->ring_fd, F_OFD_SETLK, &lock) == -1) {
        if (errno == EALREADY) {
            // Someone else owns this; this is not ours to unlink, no matter
            // what the configuration says
            recorder->unlink_file_at_close = false;
        }
        return FORMAT_ERRC(
            errno,
            "OFD wr_lock on event ring `%s` at [%ld:%ld] failed",
            recorder->file_path,
            lock.l_start,
            lock.l_len);
    }

    // TODO(ken): just because we got an advisory lock here doesn't mean we're
    //   not stomping on a completely unrelated file that was accidentally
    //   opened; later in PR2, when we have the function to read the header
    //   easily, sanity check that we're not overwriting someone else's file
    return 0;
}

// Given a description of the memory resources needed for an event ring,
// set up the ring file. This will fallocate(2) the event ring file to the
// appropriate size, mmap the header, and fill out the header structure
static int init_event_ring_file(
    struct monad_event_recorder_config const *config,
    struct monad_event_recorder *recorder)
{
    if (fallocate(
            recorder->ring_fd,
            0,
            recorder->ring_file_offset,
            (off_t)recorder->total_ring_bytes) == -1) {
        return FORMAT_ERRC(
            errno,
            "fallocate of event ring `%s` to total size %lu failed",
            recorder->file_path,
            recorder->total_ring_bytes);
    }

    // Map the header and fill it out
    struct monad_event_ring_header *header = recorder->event_ring.header = mmap(
        nullptr,
        HEADER_SIZE,
        PROT_WRITE,
        MAP_SHARED,
        recorder->ring_fd,
        recorder->ring_file_offset);
    if (header == MAP_FAILED) {
        return FORMAT_ERRC(
            errno,
            "mmap of event ring `%s` header page failed",
            recorder->file_path);
    }
    header->descriptor_capacity = 1UL << config->descriptors_shift;
    header->payload_buf_size = 1UL << config->payload_buf_shift;
    memset(&header->control, 0, sizeof header->control);
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
    struct monad_event_recorder_config const *config)
{
    int rc;
    struct monad_event_recorder *recorder;
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;

    if (recorder_p == nullptr) {
        return FORMAT_ERRC(EFAULT, "recorder_p cannot be nullptr");
    }
    *recorder_p = nullptr;
    if (config == nullptr) {
        return FORMAT_ERRC(EFAULT, "ring_config cannot be nullptr");
    }
    if (config->file_path == nullptr) {
        return FORMAT_ERRC(EFAULT, "ring_config file_path cannot be nullptr");
    }
    if (config->descriptors_shift < MONAD_EVENT_MIN_DESCRIPTORS_SHIFT ||
        config->descriptors_shift > MONAD_EVENT_MAX_DESCRIPTORS_SHIFT) {
        return FORMAT_ERRC(
            ERANGE,
            "descriptors_shift %hhu outside allowed range [%hhu, %hhu]: "
            "(ring sizes: [%lu, %lu])",
            config->descriptors_shift,
            MONAD_EVENT_MIN_DESCRIPTORS_SHIFT,
            MONAD_EVENT_MAX_DESCRIPTORS_SHIFT,
            (1UL << MONAD_EVENT_MIN_DESCRIPTORS_SHIFT),
            (1UL << MONAD_EVENT_MAX_DESCRIPTORS_SHIFT));
    }
    if (config->payload_buf_shift < MONAD_EVENT_MIN_PAYLOAD_BUF_SHIFT ||
        config->payload_buf_shift > MONAD_EVENT_MAX_PAYLOAD_BUF_SHIFT) {
        return FORMAT_ERRC(
            ERANGE,
            "payload_buf_shift %hhu outside allowed range [%hhu, %hhu]: "
            "(buffer sizes: [%lu, %lu])",
            config->payload_buf_shift,
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
    recorder->unlink_file_at_close = config->unlink_after_close;
    recorder->ring_file_offset = config->ring_file_offset;
    recorder->total_ring_bytes = monad_event_ring_calculate_size(
        1UL << config->descriptors_shift, 1UL << config->payload_buf_shift);

    recorder->file_path = strdup(config->file_path);
    if (recorder->file_path == nullptr) {
        rc = FORMAT_ERRC(
            errno, "strdup failed for file_path `%s`", config->file_path);
        goto Error;
    }

    // Open the event ring file, initialize it, and map the event ring into
    // our address space
    rc =
        open_event_ring_file(recorder, config->open_flags, config->create_mode);
    if (rc != 0) {
        goto Error;
    }
    rc = init_event_ring_file(config, recorder);
    if (rc != 0) {
        goto Error;
    }
    rc = _monad_event_ring_mmap_data(
        &recorder->event_ring,
        recorder->ring_fd,
        recorder->ring_file_offset,
        recorder->file_path);
    if (rc != 0) {
        goto Error;
    }

    // These fields are all canonically defined in the header section of the
    // shared memory file; we place them all on the same cache line in the
    // recorder, for the sake of hot path performance
    recorder->control = &recorder->event_ring.header->control;
    recorder->desc_capacity_mask =
        recorder->event_ring.header->descriptor_capacity - 1;
    recorder->payload_buf_mask =
        recorder->event_ring.header->payload_buf_size - 1;

    // Add the recorder to the global list
    pthread_mutex_lock(&rss->mtx);
    TAILQ_INSERT_TAIL(&rss->recorders, recorder, next);
    pthread_mutex_unlock(&rss->mtx);

    return 0;

Error:
    monad_event_recorder_destroy(recorder);
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
    if (recorder->next.tqe_prev != nullptr) {
        pthread_mutex_lock(&rss->mtx);
        TAILQ_REMOVE(&rss->recorders, recorder, next);
        pthread_mutex_unlock(&rss->mtx);
    }
    if (recorder->ring_fd != -1) {
        // This implies we took the lock; explicitly unlock it (in case other
        // fd's to this file are open)
        struct flock unlock = {
            .l_type = F_UNLCK,
            .l_whence = SEEK_SET,
            .l_start = recorder->ring_file_offset,
            .l_len = (off_t)recorder->total_ring_bytes,
            .l_pid = 0};
        (void)fcntl(recorder->ring_fd, F_OFD_SETLK, &unlock);
        (void)close(recorder->ring_fd);
    }
    if (recorder->unlink_file_at_close && recorder->file_path != nullptr) {
        (void)unlink(recorder->file_path);
    }
    free((void *)recorder->file_path);
    free(recorder);
}
