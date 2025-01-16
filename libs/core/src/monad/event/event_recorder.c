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

#include <fcntl.h>
#include <sys/mman.h>
#include <sys/queue.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/types.h>

#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/core/tl_tid.h>
#include <monad/event/event.h>
#include <monad/event/event_error.h>
#include <monad/event/event_metadata.h>
#include <monad/event/event_recorder.h>
#include <monad/event/event_ring_db.h>
#include <monad/event/event_types.h>

static thread_local char g_error_buf[1024];

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

static char const *EVENT_RING_TYPE_NAMES[] = {
    [MONAD_EVENT_RING_EXEC] = "exec", [MONAD_EVENT_RING_TRACE] = "trace"};

/*
 * ring db functions
 */

// Helper check function; the public API is written to force users to first
// call `monad_event_recorder_system_init`, which is the only way to obtain a
// `ring_db` object that all the other calls require. However, nothing stops
// them from proceeding to call functions even if the initialization failed.
static int check_ring_db(struct monad_event_ring_db *ring_db)
{
    if (ring_db != &g_monad_event_recorder_shared_state.ring_db) {
        return FORMAT_ERRC(
            EFAULT,
            "ring_db %p is not expected value %p",
            ring_db,
            &g_monad_event_recorder_shared_state.ring_db);
    }
    if (ring_db->db_data == nullptr) {
        return FORMAT_ERRC(
            ENXIO,
            "attempted operation on uninitialized event system;"
            "system init was not attempted or it failed");
    }
    return 0;
}

static void init_ring_db_data(struct monad_event_ring_db_data *db_data)
{
    memset(db_data, 0, sizeof *db_data);
    memcpy(
        db_data->magic,
        MONAD_EVENT_RING_DB_MAGIC,
        sizeof MONAD_EVENT_RING_DB_MAGIC);
    db_data->is_snapshot = false;
    db_data->db_version = MONAD_EVENT_RING_DB_VERSION;
    memcpy(
        db_data->metadata_hash,
        g_monad_event_metadata_hash,
        sizeof g_monad_event_metadata_hash);
    for (uint8_t r = 0; r < MONAD_EVENT_RING_COUNT; ++r) {
        struct monad_event_ring_db_entry *db_entry = &db_data->rings[r];
        // Initialize ring type and name
        db_entry->ring_type = (enum monad_event_ring_type)r;
        strncpy(
            db_entry->ring_name,
            EVENT_RING_TYPE_NAMES[r],
            sizeof db_entry->ring_name);
        db_entry->ring_data_fd = -1;
    }
}

static int
init_ring_db(char const *shm_name, struct monad_event_ring_db *ring_db)
{
    mode_t const create_mode = S_IRUSR | S_IRGRP | S_IWUSR | S_IWGRP | S_IROTH;
    int rc;
    struct flock lock = {
        .l_type = F_WRLCK,
        lock.l_whence = SEEK_SET,
        lock.l_start = 0,
        lock.l_len = sizeof *ring_db->db_data};

    memset(ring_db, 0, sizeof *ring_db);
    ring_db->pidfd = ring_db->db_fd = -1;
    ring_db->exec_pid = getpid();
    // Having a pid_fd to our own process is pointless (this field is only
    // intended for the reader API) but is set for completeness
    ring_db->pidfd = (int)syscall(SYS_pidfd_open, ring_db->exec_pid, 0);
    if (ring_db->pidfd == -1) {
        return FORMAT_ERRC(errno, "pidfd_open(2) getting our own pid failed");
    }

    // Open the ring db shared memory object; we're not using O_EXCL or O_TRUNC,
    // so we may open a currently-in-use ring db (used by an active execution
    // daemon) or a zombie one (from a dead daemon)
    ring_db->db_fd = shm_open(shm_name, O_RDWR | O_CREAT, create_mode);
    if (ring_db->db_fd == -1) {
        rc = FORMAT_ERRC(errno, "shm_open of ring db %s failed", shm_name);
        goto Error;
    }

    // Try to place a POSIX advisory lock on the ring db shared memory file;
    // if this succeeds, we're the new owner, otherwise `shm_name` is taken
    rc = fcntl(ring_db->db_fd, F_SETLK, &lock);
    if (rc == -1 && (errno == EAGAIN || errno == EACCES)) {
        // Already owned; F_SETLK doesn't set l_pid, only F_GETLK does; use
        // F_GETLK so our error message reports which pid owns the lock
        pid_t const owner_pid =
            fcntl(ring_db->db_fd, F_GETLK, &lock) != -1 ? lock.l_pid : -1;
        // POSIX allows either EAGAIN or EACCES; make EACCES canonical
        rc = FORMAT_ERRC(
            EACCES,
            "fcntl F_SETLK on ring db %s failed; locked by pid %d",
            shm_name,
            owner_pid);
        goto Error;
    }
    if (rc == -1) {
        rc = FORMAT_ERRC(
            errno, "fcntl(F_SETLK, ...) on ring db %s failed", shm_name);
        goto Error;
    }

    // Resize the ring db shared memory object to the exact size of the
    // `db_data` structure, then map the ring db contents into our process
    if (ftruncate(ring_db->db_fd, (off_t)sizeof *ring_db->db_data) == -1) {
        rc = FORMAT_ERRC(errno, "ftruncate on %s failed", shm_name);
        goto Error;
    }
    ring_db->db_data = mmap(
        nullptr,
        sizeof *ring_db->db_data,
        PROT_READ | PROT_WRITE,
        MAP_SHARED,
        ring_db->db_fd,
        0);
    if (ring_db->db_data == MAP_FAILED) {
        rc = FORMAT_ERRC(errno, "mmap of ring db %s failed", shm_name);
        goto Error;
    }

    // Initialize the db_data and set up the event recorder's db_entry
    init_ring_db_data(ring_db->db_data);
    for (uint8_t r = 0; r < MONAD_EVENT_RING_COUNT; ++r) {
        g_monad_event_recorders[r].db_entry = &ring_db->db_data->rings[r];
    }
    return 0;

Error:
    monad_event_ring_db_close(ring_db);
    return rc;
}

/*
 * Event ring functions
 */

// Mark the event ring as offline (cannot be mmap'ed) in the ring db and close
// its memfd file descriptor
static void clear_ring_db_entry(struct monad_event_ring_db_entry *db_entry)
{
    if (db_entry != nullptr) {
        __atomic_store_n(
            &db_entry->ring_control.ring_state,
            MONAD_EVENT_RING_OFFLINE,
            __ATOMIC_RELEASE);
        int const memfd =
            __atomic_exchange_n(&db_entry->ring_data_fd, -1, __ATOMIC_RELAXED);
        (void)close(memfd);
    }
}

// Given a description of the memory resources needed for an event ring in the
// ring db, "allocate" that memory and expose it in the ring db entry. All this
// does is create the memfd to hold each ring content, ftruncate(2) it to the
// appropriate size, and copy the fd into the ring db entry; no physical pages
// will be reserved until the memfd is mmap'ed into place.
static int configure_ring_db_entry(
    struct monad_event_ring_db_entry *db_entry, uint8_t ring_shift,
    uint8_t payload_buf_shift, pid_t exec_pid)
{
    char name[32];
    size_t descriptor_map_len;
    off_t ring_data_size;

    // Set the event descriptor array size parameters
    db_entry->ring_capacity = 1UL << ring_shift;
    descriptor_map_len =
        db_entry->ring_capacity * sizeof(struct monad_event_descriptor);

    // Set the event payload buffer size parameters
    db_entry->payload_buf_size = 1UL << payload_buf_shift;
    db_entry->payload_buf_map_size =
        db_entry->payload_buf_size + MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE;
    ring_data_size = (off_t)(descriptor_map_len + db_entry->payload_buf_size);

    // Create memfd descriptor and set it to the appropriate size
    snprintf(name, sizeof name, "rmfd-%s_%d", db_entry->ring_name, exec_pid);

    db_entry->ring_data_fd = memfd_create(name, MFD_CLOEXEC | MFD_HUGETLB);
    if (db_entry->ring_data_fd == -1) {
        return FORMAT_ERRC(
            errno,
            "could not create memfd for event ring %s",
            db_entry->ring_name);
    }
    if (ftruncate(db_entry->ring_data_fd, ring_data_size) == -1) {
        int const saved_errno = errno;
        (void)close(db_entry->ring_data_fd);
        return FORMAT_ERRC(
            saved_errno,
            "could not ftruncate memfd for event ring %s to size %ld",
            db_entry->ring_name,
            ring_data_size);
    }
    db_entry->ring_data_offset = 0;
    memset(&db_entry->ring_control, 0, sizeof db_entry->ring_control);
    return 0;
}

/*
 * Event recorder functions
 */

struct monad_event_recorder g_monad_event_recorders[MONAD_EVENT_RING_COUNT];

struct monad_event_recorder_shared_state g_monad_event_recorder_shared_state;

static void thread_cache_dtor(void *arg0);

// Initialization of the event recording system that happens prior to the
// process' `main` function being called. This makes the API-level init call
// implementation simpler, as we can rely on certain data structures already
// being initialized.
static void __attribute__((constructor(MONAD_EVENT_RECORDER_CTOR_PRIO)))
event_system_ctor()
{
    int rc;
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;

    rc = pthread_mutex_init(&rss->mtx, nullptr);
    MONAD_ASSERT_PRINTF(
        rc == 0, "pthread_mutex_init failed for recorder shared state mtx");
    TAILQ_INIT(&rss->thread_caches);
    rc = pthread_key_create(&rss->thread_cache_key, thread_cache_dtor);
    MONAD_ASSERT_PRINTF(
        rc == 0, "unable to create thread recorder pthread key, error: %d", rc);

    for (uint8_t r = 0; r < MONAD_EVENT_RING_COUNT; ++r) {
        struct monad_event_recorder *recorder = &g_monad_event_recorders[r];
        memset(recorder, 0, sizeof *recorder);
        rc = pthread_mutex_init(&recorder->config_mtx, nullptr);
        MONAD_ASSERT_PRINTF(
            rc == 0, "pthread_mutex_init failed during recorder %hhu init", r);
    }
}

// Cleanup routine that runs automatically after `main` returns or libc
// exit(3) is called; frees the resources taken in the above constructor
static void __attribute__((destructor(MONAD_EVENT_RECORDER_CTOR_PRIO)))
event_system_dtor()
{
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;

    if (rss->shm_name != nullptr) {
        shm_unlink(rss->shm_name);
        free(rss->shm_name);
    }
    for (uint8_t r = 0; r < MONAD_EVENT_RING_COUNT; ++r) {
        struct monad_event_recorder *recorder = &g_monad_event_recorders[r];
        monad_event_ring_unmap(&recorder->event_ring);
        clear_ring_db_entry(recorder->db_entry);
        pthread_mutex_destroy(&recorder->config_mtx);
    }
    monad_event_ring_db_close(&rss->ring_db);
    pthread_key_delete(rss->thread_cache_key);
    pthread_mutex_destroy(&rss->mtx);
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

int monad_event_recorder_system_init(
    char const *shm_name, struct monad_event_ring_db **ring_db)
{
    int rc;
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;

    if (ring_db == nullptr) {
        return FORMAT_ERRC(EFAULT, "ring_db cannot be nullptr");
    }
    if (shm_name == nullptr) {
        shm_name = MONAD_EVENT_DEFAULT_RING_DB_SHM_NAME;
    }
    rss->shm_name = strdup(shm_name);
    if (rss->shm_name == nullptr) {
        return FORMAT_ERRC(errno, "strdup(3) of %s failed", shm_name);
    }

    pthread_mutex_lock(&rss->mtx);
    if (rss->ring_db.db_data != nullptr) {
        rc = FORMAT_ERRC(EBUSY, "event system already initialized");
        goto UnlockReturn;
    }
    rc = init_ring_db(rss->shm_name, &rss->ring_db);

UnlockReturn:
    *ring_db = &rss->ring_db;
    pthread_mutex_unlock(&rss->mtx);
    return rc;
}

int monad_event_recorder_configure(
    struct monad_event_ring_db *ring_db, enum monad_event_ring_type ring_type,
    uint8_t ring_shift, uint8_t payload_buf_shift)
{
    int rc;
    struct monad_event_ring_control *rctl;
    struct monad_event_recorder *recorder;
    struct monad_event_ring_db_entry *db_entry;
    enum monad_event_ring_state ring_state;
    struct ring_size_params const *rsp;

    if (ring_type >= MONAD_EVENT_RING_COUNT) {
        return FORMAT_ERRC(
            EINVAL, "ring_type %hhu is not a valid value", ring_type);
    }
    if (ring_shift == 0) {
        ring_shift = s_ring_size_params[ring_type].default_ring_shift;
    }
    if (payload_buf_shift == 0) {
        payload_buf_shift =
            s_ring_size_params[ring_type].default_payload_buf_shift;
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

    if ((rc = check_ring_db(ring_db)) != 0) {
        return rc;
    }
    recorder = &g_monad_event_recorders[ring_type];
    db_entry = &ring_db->db_data->rings[ring_type];
    rctl = &db_entry->ring_control;

    // Lock config_mtx to configure the event ring memory parameters;
    // technically this mutex protects the ring db entry, not the recorder.
    // However, the `*db_entry` lives in shared memory and configuration is
    // something only the writer process can do, so we own the mutex.
    pthread_mutex_lock(&recorder->config_mtx);

    ring_state = __atomic_load_n(&rctl->ring_state, __ATOMIC_ACQUIRE);
    if (ring_state != MONAD_EVENT_RING_OFFLINE) {
        // The event ring already is mapped (i.e., recorder.event_ring->control
        // is potentially cached by other threads in the reader) so we cannot
        // safely reconfigure the ring
        rc = FORMAT_ERRC(
            EBUSY,
            "recorder for event ring %s cannot be reconfigured",
            db_entry->ring_name);
        goto UnlockReturn;
    }

    // Set up the ring db entry for this event ring; this also creates an
    // appropriately-sized memfd_create(2) descriptor for all parts of the
    // event ring, since that fd is part of the db entry
    rc = configure_ring_db_entry(
        db_entry, ring_shift, payload_buf_shift, ring_db->exec_pid);
    if (rc != 0) {
        goto UnlockReturn;
    }

    // Map the event ring into our process' address space
    rc = monad_event_ring_db_import(ring_db, ring_type, &recorder->event_ring);
    if (rc != 0) {
        clear_ring_db_entry(db_entry);
        FORMAT_ERRC(
            rc,
            "failed to import event ring %s: %s",
            db_entry->ring_name,
            monad_event_ring_db_get_last_error());
    }
    else {
        __atomic_store_n(
            &rctl->ring_state, MONAD_EVENT_RING_CONFIGURED, __ATOMIC_RELEASE);
    }

UnlockReturn:
    pthread_mutex_unlock(&recorder->config_mtx);
    return rc;
}

struct monad_event_ring const *monad_event_recorder_get_event_ring(
    struct monad_event_ring_db *ring_db, enum monad_event_ring_type ring_type)
{
    struct monad_event_recorder *recorder;
    enum monad_event_ring_state ring_state;
    if (ring_type >= MONAD_EVENT_RING_COUNT) {
        (void)FORMAT_ERRC(EINVAL, "%hhu is not a valid ring type", ring_type);
        return nullptr;
    }
    if (check_ring_db(ring_db) != 0) {
        return nullptr;
    }
    recorder = &g_monad_event_recorders[ring_type];
    ring_state = __atomic_load_n(
        &recorder->db_entry->ring_control.ring_state, __ATOMIC_ACQUIRE);
    return ring_state == MONAD_EVENT_RING_OFFLINE ? nullptr
                                                  : &recorder->event_ring;
}

char const *monad_event_recorder_get_last_error()
{
    return g_error_buf;
}

/*
 * Thread cache functions
 */

thread_local struct monad_event_recorder_thr g_tls_monad_recorder_thread_cache;

// Destructor for thread_local `struct monad_event_recorder_thr` objects;
// called when a thread exits or the process ends, whichever happens first
static void thread_cache_dtor(void *arg0)
{
    struct monad_event_recorder_thr *const thread_cache = arg0;
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;

    // Record the termination of this thread
    MONAD_EVENT(MONAD_EVENT_THREAD_EXIT, 0);

    // Give back the source_id for this thread, and remove the thread's recorder
    // state object from the global list
    pthread_mutex_lock(&rss->mtx);
    rss->thread_source_ids &= ~(uint64_t)(1UL << (thread_cache->source_id - 1));
    TAILQ_REMOVE(&rss->thread_caches, thread_cache, next);
    pthread_mutex_unlock(&rss->mtx);
}

// Constructor for thread_local `struct monad_event_recorder_thr` objects,
// called when a thread records an event for the first time.
//
// This emits a MONAD_EVENT_THREAD_CREATE event with metadata about the thread,
// allocates a "source id" that refers to this thread, and also copies the
// thread metadata into the thread_info metadata array (indexed by the source
// ID). This is done for the benefit of late-running utilities that import the
// event ring after the original `MONAD_EVENT_THREAD_CREATE` has expired
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
    local_thread_info.process_id = (uint64_t)rss->ring_db.exec_pid;
    local_thread_info.thread_id = thread_cache->thread_id =
        (uint64_t)get_tl_tid();
    (void)pthread_getname_np(
        pthread_self(),
        local_thread_info.thread_name,
        sizeof local_thread_info.thread_name);

    // Reserve a source_id for this thread recorder, add it to the global list
    pthread_mutex_lock(&rss->mtx);
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
    thread_info = &rss->ring_db.db_data->thread_info[s];
    memcpy(thread_info, &local_thread_info, sizeof local_thread_info);
    TAILQ_INSERT_TAIL(&rss->thread_caches, thread_cache, next);
    pthread_setspecific(rss->thread_cache_key, thread_cache);
    pthread_mutex_unlock(&rss->mtx);

    // Announce the creation of this thread
    MONAD_EVENT_EXPR(MONAD_EVENT_THREAD_CREATE, 0, *thread_info);
}

__attribute__((weak)) uint32_t monad_event_get_txn_id()
{
    return 0;
}
