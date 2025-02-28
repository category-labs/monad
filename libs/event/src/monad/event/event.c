#include <errno.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

#include <fcntl.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <unistd.h>

#include <monad/event/event.h>
#include <monad/event/event_error.h>
#include <monad/event/event_metadata.h>

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

static int import_ring_data_fd(
    pid_t owner, int owner_fd, char const *error_name, int *our_fd)
{
    char proc_fd_path[32];

    snprintf(
        proc_fd_path, sizeof proc_fd_path, "/proc/%d/fd/%d", owner, owner_fd);
    *our_fd = open(proc_fd_path, O_RDONLY);
    if (*our_fd == -1) {
        return FORMAT_ERRC(
            errno,
            "open of event ring `%s` foreign memfd %d failed",
            error_name,
            owner_fd);
    }

    return 0;
}

// Given an open ring_fd, try to mmap a view of the header structure and
// validate it. Validate means that it appears to be a correct header and its
// contents are compatible with our version of the event library. This also
// opens a pidfd to the execution process that owns the event ring file.
//
// Although this function is primarily meant for readers, it has external
// linkage because the writer calls it. If the writer fails to obtain an
// exclusive flock(2) on the shared memory file, it uses this function to
// report the pid of the process that owns the lock.
int _monad_event_ring_mmap_header(
    int ring_fd, char const *error_name, int *pidfd,
    struct monad_event_ring_header **header_p)
{
    int rc;
    struct monad_event_ring_header *header;

    *header_p = header =
        mmap(nullptr, PAGE_2MB, PROT_READ, MAP_SHARED, ring_fd, 0);
    if (header == MAP_FAILED) {
        return FORMAT_ERRC(
            errno, "mmap of event ring `%s` header failed", error_name);
    }
    // Perform various ABI compatibility checks
    if (memcmp(
            header->version,
            MONAD_EVENT_RING_HEADER_VERSION,
            sizeof MONAD_EVENT_RING_HEADER_VERSION) != 0) {
        rc = FORMAT_ERRC(
            EPROTO,
            "wrong magic number in event ring`%s`; not a ring db file",
            error_name);
        goto Error;
    }
    if (memcmp(
            header->metadata_hash,
            g_monad_event_metadata_hash,
            sizeof g_monad_event_metadata_hash) != 0) {
        rc = FORMAT_ERRC(
            EPROTO,
            "event ring `%s` metadata hash does not match "
            "loaded library version",
            error_name);
        goto Error;
    }
    *pidfd = (int)syscall(SYS_pidfd_open, header->writer_pid, 0);
    if (*pidfd == -1) {
        if (errno == ESRCH) {
            rc = FORMAT_ERRC(
                EOWNERDEAD, "writer of event ring `%s` is gone", error_name);
        }
        else {
            rc = FORMAT_ERRC(
                errno,
                "pidfd_open error on event ring `%s` pid %d",
                error_name,
                header->writer_pid);
        }
        goto Error;
    }
    return 0;

Error:
    munmap(header, PAGE_2MB);
    *header_p = nullptr;
    return rc;
}

// This helper function will mmap the non-header parts of the event ring file;
// it is used by both the reader and writer code. The normal event ring file
// layout is divided into sections, where each section is aligned to 2 MiB
// large page boundary:
//
//  .------------------.
//  |   Ring header    |
//  .------------------.
//  | Descriptor array |
//  .------------------.
//  |  Payload buffer  |
//  .------------------.
//  |   Primary ring   |
//  |     metadata     |
//  |     (optional)   |
//  .------------------.
//
// Until we have hugetlbfs support, a second format is supported: the header
// is in a small file by itself, and it describes how to load the real event
// ring data file that contains the other sections, which require huge page
// support. In that case, this secondary ring data file is an anonymous
// memfd_create(2) descriptor that we need to import from the writer process
int _monad_event_ring_mmap_data(
    struct monad_event_ring *event_ring, int ring_fd, char const *error_name)
{
    int ring_data_fd;
    int rc;
    size_t descriptor_map_len;
    off_t base_ring_data_offset;
    struct monad_event_ring_header const *const header = event_ring->header;
    bool const is_writer = header->writer_pid == getpid();
    int const mmap_prot = is_writer ? PROT_READ | PROT_WRITE : PROT_READ;

    // Set `ring_data_fd` to a file descriptor that contains the data
    // structures of an event ring. There are three cases:
    //
    //   1. This is a normal event ring file (e.g., using hugetlbfs). The event
    //      ring data structures are in the same file as the header.
    //
    //   2. This is a "discovery only" event ring file, and we are the writer
    //      process. In this case, the `ring_data_fd` field in the header will
    //      be our own process' memfd_create(2) file descriptor.
    //
    //   3. This is a "discovery only" event ring, and we are a reader process.
    //      In this case, the `ring_data_fd` field in the header is an fd in
    //      the file descriptor table of the writer process rather than our
    //      own. We have to open it for ourselves first, using the symlink to
    //      it in the writer's `/proc/<pid>/fd` directory (see proc(5)).
    if (header->is_discovery == false) {
        // Case 1: all event ring structures are in the same file
        ring_data_fd = ring_fd;
        base_ring_data_offset = (off_t)PAGE_2MB;
    }
    else if (is_writer) {
        // Case 2: header is a "discovery only" file, and we're the writer;
        // header->data_fd has the data, and is our own fd
        ring_data_fd = header->data_fd;
        base_ring_data_offset = 0;
    }
    else {
        // Case 3: like case 2, but header->data_fd is a file descriptor in the
        // writer's file descriptor table, not in our own; we need to open it
        // ourselves using helper function
        rc = import_ring_data_fd(
            header->writer_pid, header->data_fd, error_name, &ring_data_fd);
        if (rc != 0) {
            return rc;
        }
        base_ring_data_offset = 0;
    }

    // Map the ring descriptor array from the ring data fd
    descriptor_map_len =
        header->ring_capacity * sizeof(struct monad_event_descriptor);
    event_ring->descriptors = mmap(
        nullptr,
        descriptor_map_len,
        mmap_prot,
        MAP_SHARED | MAP_POPULATE | MAP_HUGETLB,
        ring_data_fd,
        base_ring_data_offset);
    if (event_ring->descriptors == MAP_FAILED) {
        rc = FORMAT_ERRC(
            errno,
            "mmap of event ring `%s` event descriptor array failed",
            error_name);
        goto Error;
    }

    // The mmap step of the payload buffer is more complex: first, reserve a
    // single anonymous mapping whose size is twice the size of the payload
    // buffer, so we can do the "wrap around" trick. We'll remap the actual
    // payload buffer fd into this reserved range later, using MAP_FIXED.
    event_ring->payload_buf = mmap(
        nullptr,
        2 * header->payload_buf_size,
        mmap_prot,
        MAP_SHARED | MAP_ANONYMOUS | MAP_HUGETLB,
        -1,
        base_ring_data_offset + (off_t)descriptor_map_len);
    if (event_ring->payload_buf == MAP_FAILED) {
        rc = FORMAT_ERRC(
            errno,
            "mmap of event ring `%s` payload buffer anonymous region failed",
            error_name);
        goto Error;
    }

    // Map the payload buffer into the first part of the space we just reserved
    if (mmap(
            event_ring->payload_buf,
            header->payload_buf_size,
            mmap_prot,
            MAP_FIXED | MAP_SHARED | MAP_POPULATE | MAP_HUGETLB,
            ring_data_fd,
            base_ring_data_offset + (off_t)descriptor_map_len) == MAP_FAILED) {
        rc = FORMAT_ERRC(
            errno,
            "fixed mmap of event ring `%s` payload buffer to %p failed",
            error_name,
            event_ring->payload_buf);
        goto Error;
    }

    // Map the "wrap around" view of the payload buffer immediately after the
    // previous mapping. This allows memcpy(3) to naturally "wrap around" in
    // memory by the size of one maximally-sized event. Thus, we can copy event
    // payloads safely near the end of the buffer, without needing to do any
    // error-prone index massaging.
    if (mmap(
            event_ring->payload_buf + header->payload_buf_size,
            header->payload_buf_size,
            mmap_prot,
            MAP_FIXED | MAP_SHARED | MAP_POPULATE | MAP_HUGETLB,
            ring_data_fd,
            base_ring_data_offset + (off_t)descriptor_map_len) == MAP_FAILED) {
        rc = FORMAT_ERRC(
            errno,
            "fixed mmap event ring `%s` payload buffer wrap-around pages at %p "
            "failed",
            error_name,
            event_ring->payload_buf + header->payload_buf_size);
        goto Error;
    }

    if (header->is_primary) {
        // The primary event ring is the one whose shared memory file hosts
        // the metadata referred in the event descriptor's "ID" fields
        event_ring->blocks = mmap(
            nullptr,
            PAGE_2MB,
            mmap_prot,
            MAP_SHARED | MAP_POPULATE | MAP_HUGETLB,
            ring_data_fd,
            base_ring_data_offset + (off_t)descriptor_map_len +
                (off_t)header->payload_buf_size);
        if (event_ring->blocks == MAP_FAILED) {
            rc = FORMAT_ERRC(
                errno,
                "mmap of event ring `%s` ID metadata failed",
                error_name);
            goto Error;
        }
    }

    if (!is_writer && ring_data_fd != ring_fd) {
        (void)close(ring_data_fd);
    }
    return 0;

Error:
    monad_event_ring_unmap(event_ring);
    if (!is_writer && ring_data_fd != ring_fd) {
        (void)close(ring_data_fd);
    }
    return rc;
}

int monad_event_ring_map(
    struct monad_event_ring *event_ring, char const *file_path, int *pidfd)
{
    int ring_fd;
    int rc;
    int local_pidfd;

    if (event_ring == nullptr) {
        return FORMAT_ERRC(EFAULT, "event_ring cannot be nullptr");
    }
    if (file_path == nullptr) {
        return FORMAT_ERRC(EFAULT, "file_path cannot be nullptr");
    }
    memset(event_ring, 0, sizeof *event_ring);
    ring_fd = open(file_path, O_RDONLY);
    if (ring_fd == -1) {
        return FORMAT_ERRC(errno, "open of event ring `%s` failed", file_path);
    }
    rc = _monad_event_ring_mmap_header(
        ring_fd, file_path, &local_pidfd, &event_ring->header);
    if (rc != 0) {
        monad_event_ring_unmap(event_ring);
        return rc;
    }
    rc = _monad_event_ring_mmap_data(event_ring, ring_fd, file_path);
    if (rc != 0) {
        monad_event_ring_unmap(event_ring);
        return rc;
    }
    if (pidfd != nullptr) {
        *pidfd = local_pidfd;
    }
    else {
        (void)close(local_pidfd);
    }
    return 0;
}

void monad_event_ring_unmap(struct monad_event_ring *event_ring)
{
    struct monad_event_ring_header const *const header = event_ring->header;
    if (header != nullptr) {
        if (event_ring->descriptors) {
            munmap(
                event_ring->descriptors,
                header->ring_capacity * sizeof(struct monad_event_descriptor));
        }
        if (event_ring->payload_buf) {
            munmap(event_ring->payload_buf, 2 * header->payload_buf_size);
        }
        if (event_ring->blocks) {
            munmap(event_ring->blocks, PAGE_2MB);
        }
        // We don't do anything with `event_ring->blocks`, it's on the same
        // PAGE_2MB-sized mapping as the thread metadata
        munmap((void *)header, PAGE_2MB);
    }
    memset(event_ring, 0, sizeof *event_ring);
}

char const *monad_event_ring_get_last_error()
{
    return g_error_buf;
}
