/**
 * @file
 *
 * This file contains the implementation of the ring db interface.
 *
 * The rationale for the ring db is to separate the event ring itself (which
 * is just a `struct monad_event_ring`) from all the IPC mechanisms needed to
 * publicly describe it to other processes, and allow those other processes
 * to import it. The latter is handled by the ring db. The execution daemon's
 * "recorder" infrastructure creates the ring db, but also reuses the
 * monad_event_ring_db_import function to import event rings into its own
 * address space, in the same way an external process would.
 *
 * The two primary data structures of the event ring (the descriptor array and
 * payload buffer) are allocated using the Linux-specific memfd_create(2)
 * system call. This is because shared memory segments created with other APIs
 * (e.g., POSIX shm_open) cannot be mmap'ed with MAP_HUGETLB support. Because
 * memfd segments are anonymous, we need a metadata structure that can be
 * looked up by other processes by name, to help us locate and import event
 * rings. Alternative implementations are possible (e.g., using hugetlbfs, see
 * event_recorder.md for a discussion) but have similar complexity.
 *
 * The ring db is usually a POSIX shared memory file (from shm_open) that is
 * created and maintained by a running execution daemon. The ring db can also
 * be a regular file, in which case it describes a snapshot of event ring
 * shared memory that has been persisted to disk for the sake of making replay
 * testing easier. In that case, the file also contains a snapshot of the
 * execution event ring contents, at an offset following the
 * `struct monad_event_ring_db_data` instance.
 */

#include <assert.h>
#include <errno.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

#include <fcntl.h>
#include <poll.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <unistd.h>

#include <monad/event/event_error.h>
#include <monad/event/event_metadata.h>
#include <monad/event/event_ring_db.h>

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

// Return an open file descriptor that when mmap'ed, contains the primary data
// structures of an event ring. There are three cases:
//
//   1. This is a "fake" ring db, describing a snapshot of shared memory
//      persisted to a file. These are used for testing purposes. In this case,
//      the event ring memory is in the same file as ring db itself.
//
//   2. This is a real ring db, and we are the writer process. In this case,
//      the `ring_data_fd` field in the db entry will be our own process'
//      memfd_create(2) file descriptor.
//
//   3. This is a real ring db, and we are a reader process. This is similar
//      to above case, except the file descriptor is an fd in the fd namespace
//      of the writer process rather than our own. We have to open it using the
//      symlink to it in the writer's `/proc/<pid>/fd` directory (see proc(5)).
static int lookup_ring_fd(
    struct monad_event_ring_db const *ring_db,
    enum monad_event_ring_type ring_type, bool is_writer, int *fd)
{
    char proc_fd_path[32];
    struct monad_event_ring_db_entry const *const db_entry =
        &ring_db->db_data->rings[ring_type];

    if (ring_db->db_data->is_snapshot) {
        // Case 1: this is a persisted snapshot file
        *fd = ring_db->db_fd;
        return 0;
    }
    *fd = __atomic_load_n(&db_entry->ring_data_fd, __ATOMIC_RELAXED);
    if (is_writer) {
        // Case 2: we're the writer, so *fd is our own fd
        return 0;
    }

    // Case 3: *fd is a file descriptor in the writer's process, not in our
    // own; to mmap it, we need to open it ourselves
    snprintf(
        proc_fd_path,
        sizeof proc_fd_path,
        "/proc/%d/fd/%d",
        ring_db->exec_pid,
        *fd);
    *fd = open(proc_fd_path, O_RDONLY);
    if (*fd == -1) {
        return FORMAT_ERRC(
            errno,
            "open of event ring %s foreign memfd %s failed",
            db_entry->ring_name,
            proc_fd_path);
    }

    // Since we looked in /proc/<pid>, ensure that this is actually still the
    // same process and not a later one reusing the same pid
    if (!monad_event_ring_db_is_alive(ring_db)) {
        (void)close(*fd);
        *fd = -1;
        return FORMAT_ERRC(
            EOWNERDEAD, "execution daemon %d is gone", ring_db->exec_pid);
    }
    return 0;
}

int monad_event_ring_db_open(
    struct monad_event_ring_db *ring_db, char const *shm_name)
{
    struct flock lock;
    int rc;

    if (shm_name == nullptr) {
        shm_name = MONAD_EVENT_DEFAULT_RING_DB_SHM_NAME;
    }
    if (ring_db == nullptr) {
        return FORMAT_ERRC(EFAULT, "ring_db cannot be nullptr");
    }

    memset(ring_db, 0, sizeof *ring_db);
    ring_db->pidfd = ring_db->db_fd = -1;

    // Open the ring db shared memory object
    ring_db->db_fd = shm_open(shm_name, O_RDONLY, 0);
    if (ring_db->db_fd == -1) {
        return FORMAT_ERRC(errno, "shm_open of `%s` failed", shm_name);
    }

    // Map the ring db contents into our process
    ring_db->db_data = mmap(
        nullptr,
        sizeof *ring_db->db_data,
        PROT_READ,
        MAP_SHARED,
        ring_db->db_fd,
        0);
    if (ring_db->db_data == MAP_FAILED) {
        rc = FORMAT_ERRC(errno, "mmap of ring db `%s` failed", shm_name);
        goto Error;
    }

    // Query which process holds the lock on the ring db file; this is used to
    // detect the execution process' pid
    lock.l_type = F_RDLCK;
    lock.l_whence = SEEK_SET;
    lock.l_start = 0;
    lock.l_len = sizeof *ring_db->db_data;
    if (fcntl(ring_db->db_fd, F_GETLK, &lock) == -1) {
        rc = FORMAT_ERRC(errno, "could not get query flock on `%s`", shm_name);
        goto Error;
    }
    if (ring_db->db_data->is_snapshot) {
        // Snapshots don't have an associated execution process
        ring_db->exec_pid = -1;
    }
    else if (lock.l_type == F_UNLCK) {
        // An explicitly unlocked ring db indicates the execution daemon is dead
        rc = FORMAT_ERRC(EOWNERDEAD, "ring db `%s` appears orphaned", shm_name);
        goto Error;
    }
    else if (lock.l_type != F_WRLCK || lock.l_pid == -1) {
        // These cases are strange: we see a lock, but not the kind our locking
        // protocol specifies should be placed (this is either a shared lock, or
        // a Linux-style lock without a pid). We do not know what this means.
        rc = FORMAT_ERRC(
            EPROTO,
            "ring db `%s` holds unexpected lock %hu:%d",
            shm_name,
            lock.l_type,
            lock.l_pid);
        goto Error;
    }
    else {
        // The good case: a still-alive process has write-locked the ring db;
        // this process is the execution daemon
        assert(lock.l_type == F_WRLCK && lock.l_pid != -1);
        ring_db->exec_pid = lock.l_pid;
    }

    // Get a pidfd to the process that owns the ring db, or to our own process
    // in the snapshot case
    ring_db->pidfd = ring_db->exec_pid == -1
                         ? (int)syscall(SYS_pidfd_open, getpid(), 0)
                         : (int)syscall(SYS_pidfd_open, ring_db->exec_pid, 0);
    if (ring_db->pidfd == -1) {
        if (errno == ESRCH) {
            // Process died between the F_GETLK and now; report this as
            // EOWNERDEAD instead of ESRCH to match the unlocked file case
            rc = FORMAT_ERRC(
                EOWNERDEAD, "ring db `%s` appears orphaned", shm_name);
        }
        else {
            rc = FORMAT_ERRC(
                errno,
                "pidfd_open failed for pid %d while "
                "trying to open ring db `%s`",
                ring_db->exec_pid,
                shm_name);
        }
        goto Error;
    }

    // Perform various ABI compatibility checks
    if (memcmp(
            ring_db->db_data->magic,
            MONAD_EVENT_RING_DB_MAGIC,
            sizeof MONAD_EVENT_RING_DB_MAGIC) != 0) {
        rc = FORMAT_ERRC(
            EPROTO,
            "wrong magic number in ring db `%s`; not a ring db file",
            shm_name);
        goto Error;
    }
    if (ring_db->db_data->db_version != MONAD_EVENT_RING_DB_VERSION) {
        rc = FORMAT_ERRC(
            EPROTO,
            "ring db `%s` uses version %u but loaded "
            "library version is %u",
            shm_name,
            ring_db->db_data->db_version,
            MONAD_EVENT_RING_DB_VERSION);
        goto Error;
    }
    if (memcmp(
            ring_db->db_data->metadata_hash,
            g_monad_event_metadata_hash,
            sizeof g_monad_event_metadata_hash) != 0) {
        rc = FORMAT_ERRC(
            EPROTO,
            "ring db `%s` metadata hash does not match "
            "loaded library version",
            shm_name);
        goto Error;
    }
    return 0;

Error:
    monad_event_ring_db_close(ring_db);
    return rc;
}

void monad_event_ring_db_close(struct monad_event_ring_db *ring_db)
{
    assert(ring_db != nullptr);
    (void)close(ring_db->pidfd);
    (void)close(ring_db->db_fd);
    if (ring_db->db_data != nullptr) {
        munmap(ring_db->db_data, sizeof *ring_db->db_data);
    }
}

bool monad_event_ring_db_is_alive(struct monad_event_ring_db const *ring_db)
{
    struct pollfd pfd = {.fd = ring_db->pidfd, .events = POLLIN, .revents = 0};
    // We have a Linux pidfd for the execution process. It has exited if the
    // descriptor is readable, per pidfd_open(2). We also report it as dead if
    // poll(2) fails. For snapshots, it refers to our own pid, so always alive.
    bool const is_dead =
        poll(&pfd, 1, 0) == -1 || (pfd.revents & POLLIN) == POLLIN;
    return !is_dead;
}

int monad_event_ring_db_import(
    struct monad_event_ring_db const *ring_db,
    enum monad_event_ring_type ring_type, struct monad_event_ring *event_ring)
{
    int rc;
    size_t descriptor_map_len;
    int ring_data_fd = -1;
    bool const is_writer = getpid() == ring_db->exec_pid;
    bool const should_close_fd = !is_writer && !ring_db->db_data->is_snapshot;
    int const mmap_prot = PROT_READ | (is_writer ? PROT_WRITE : 0);
    int const mmap_huge = ring_db->db_data->is_snapshot ? 0 : MAP_HUGETLB;
    struct monad_event_ring_db_entry const *const db_entry =
        &ring_db->db_data->rings[ring_type];

    memset(event_ring, 0, sizeof *event_ring);
    // Check if the ring is offline. This check is only performed for readers:
    // the writer uses this function to import the event ring before changing
    // its state from OFFLINE to CONFIGURED
    if (!is_writer &&
        __atomic_load_n(&db_entry->ring_control.ring_state, __ATOMIC_ACQUIRE) ==
            MONAD_EVENT_RING_OFFLINE) {
        return FORMAT_ERRC(
            ENODEV,
            "cannot import disabled event ring %s",
            db_entry->ring_name);
    }

    event_ring->capacity = db_entry->ring_capacity;
    event_ring->payload_buf_size = db_entry->payload_buf_size;

    // An event ring's control structure is actually part of the ring db.
    // Rather than reference it at that address, each event ring mmap's the
    // entire ring database as its own unique shared mapping, then references
    // `control` from that new address. This is almost free: we'll only need
    // one additional page table entry, and no additional physical pages.
    // The rationale here is that without this, the user would need to be
    // careful not to use an event ring after calling monad_event_ring_db_close,
    // or a memory access fault would occur. Doing it this way results in a
    // less error-prone API: you can call monad_event_ring_db_close and
    // monad_event_ring_unmap in either order.
    event_ring->ring_db_map_base = mmap(
        nullptr,
        sizeof *ring_db->db_data,
        mmap_prot,
        MAP_SHARED,
        ring_db->db_fd,
        0);
    if (event_ring->ring_db_map_base == MAP_FAILED) {
        rc = FORMAT_ERRC(
            errno,
            "duplicate mmap of ring_db for event ring %s failed",
            db_entry->ring_name);
        goto Error;
    }
    event_ring->control =
        &((struct monad_event_ring_db_data *)event_ring->ring_db_map_base)
             ->rings[ring_type]
             .ring_control;

    // Look up the event ring contents fd and map the ring descriptor array
    // from it
    rc = lookup_ring_fd(ring_db, ring_type, is_writer, &ring_data_fd);
    if (rc != 0) {
        goto Error;
    }
    descriptor_map_len =
        db_entry->ring_capacity * sizeof(struct monad_event_descriptor);
    event_ring->descriptors = mmap(
        nullptr,
        descriptor_map_len,
        mmap_prot,
        MAP_SHARED | MAP_POPULATE | mmap_huge,
        ring_data_fd,
        db_entry->ring_data_offset);
    if (event_ring->descriptors == MAP_FAILED) {
        rc = FORMAT_ERRC(
            errno,
            "mmap of event ring %s event descriptor array failed",
            db_entry->ring_name);
        goto Error;
    }

    // The mmap step of the payload buffer is more complex: first, reserve a
    // single anonymous mapping whose size encompasses both the nominal size
    // of the payload buffer plus the size of the wrap-around large pages.
    // We'll remap the actual payload buffer fd into this reserved range
    // later, using MAP_FIXED.
    event_ring->payload_buf = mmap(
        nullptr,
        db_entry->payload_buf_size + MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE,
        mmap_prot,
        MAP_SHARED | MAP_ANONYMOUS | mmap_huge,
        -1,
        0);
    if (event_ring->payload_buf == MAP_FAILED) {
        rc = FORMAT_ERRC(
            errno,
            "mmap of event ring %s payload buffer anonymous region failed",
            db_entry->ring_name);
        goto Error;
    }

    // Map the payload buffer into the first part of the space we just reserved
    if (mmap(
            event_ring->payload_buf,
            db_entry->payload_buf_size,
            mmap_prot,
            MAP_FIXED | MAP_SHARED | MAP_POPULATE | mmap_huge,
            ring_data_fd,
            db_entry->ring_data_offset + (off_t)descriptor_map_len) ==
        MAP_FAILED) {
        rc = FORMAT_ERRC(
            errno,
            "fixed mmap of event ring %s payload buffer to %p failed",
            db_entry->ring_name,
            event_ring->payload_buf);
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
            event_ring->payload_buf + db_entry->payload_buf_size,
            MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE,
            mmap_prot,
            MAP_FIXED | MAP_SHARED | MAP_POPULATE | mmap_huge,
            ring_data_fd,
            db_entry->ring_data_offset + (off_t)descriptor_map_len) ==
        MAP_FAILED) {
        rc = FORMAT_ERRC(
            errno,
            "fixed mmap event ring %s payload buffer wrap-around pages at %p "
            "failed",
            db_entry->ring_name,
            event_ring->payload_buf + db_entry->payload_buf_size);
        goto Error;
    }
    if (should_close_fd) {
        (void)close(ring_data_fd);
    }

    return 0;

Error:
    // At least one mapping failed; close file we opened and remove any
    // partially mapped event ring
    if (should_close_fd) {
        (void)close(ring_data_fd);
    }
    monad_event_ring_unmap(event_ring);
    return rc;
}

char const *monad_event_ring_db_get_last_error()
{
    return g_error_buf;
}

void monad_event_ring_unmap(struct monad_event_ring *event_ring)
{
    if (event_ring->ring_db_map_base != nullptr) {
        munmap(
            event_ring->ring_db_map_base,
            sizeof(struct monad_event_ring_db_data));
    }
    if (event_ring->descriptors != nullptr) {
        munmap(
            event_ring->descriptors,
            event_ring->capacity * sizeof(struct monad_event_descriptor));
    }
    if (event_ring->payload_buf != nullptr) {
        munmap(
            event_ring->payload_buf,
            event_ring->payload_buf_size + MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE);
    }
    memset(event_ring, 0, sizeof *event_ring);
}
