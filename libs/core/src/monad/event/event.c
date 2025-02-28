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

#include <monad/core/format_err.h>
#include <monad/event/event.h>
#include <monad/event/event_metadata.h>

thread_local char _g_monad_event_error_buf[1024];
static size_t const PAGE_2MB = 1UL << 21;

#define FORMAT_ERRC(...)                                                       \
    monad_format_err(                                                          \
        _g_monad_event_error_buf,                                              \
        sizeof(_g_monad_event_error_buf),                                      \
        &MONAD_SOURCE_LOCATION_CURRENT(),                                      \
        __VA_ARGS__)

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
int _monad_event_ring_mmap_data(
    struct monad_event_ring *event_ring, int ring_fd, char const *error_name)
{
    int rc;
    size_t descriptor_map_len;
    off_t const base_ring_data_offset = (off_t)PAGE_2MB;
    struct monad_event_ring_header const *const header = event_ring->header;
    bool const is_writer = header->writer_pid == getpid();
    int const mmap_prot = is_writer ? PROT_READ | PROT_WRITE : PROT_READ;

    // Map the ring descriptor array from the ring fd
    descriptor_map_len =
        header->ring_capacity * sizeof(struct monad_event_descriptor);
    event_ring->descriptors = mmap(
        nullptr,
        descriptor_map_len,
        mmap_prot,
        MAP_SHARED | MAP_POPULATE | MAP_HUGETLB,
        ring_fd,
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
            ring_fd,
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
            ring_fd,
            base_ring_data_offset + (off_t)descriptor_map_len) == MAP_FAILED) {
        rc = FORMAT_ERRC(
            errno,
            "fixed mmap event ring `%s` payload buffer wrap-around pages at %p "
            "failed",
            error_name,
            event_ring->payload_buf + header->payload_buf_size);
        goto Error;
    }

    return 0;

Error:
    monad_event_ring_unmap(event_ring);
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
        munmap((void *)header, PAGE_2MB);
    }
    memset(event_ring, 0, sizeof *event_ring);
}

char const *monad_event_get_last_error()
{
    return _g_monad_event_error_buf;
}
