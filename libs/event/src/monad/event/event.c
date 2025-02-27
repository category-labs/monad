#include <errno.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

#include <fcntl.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <unistd.h>

#include <monad/event/event.h>
#include <monad/event/event_error.h>

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
    int const mmap_prot = PROT_READ | PROT_WRITE;

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
    else {
        // Cases 2 and 3: header is a "discovery only" file
        // TODO(ken): we don't distinguish between the reader and writer yet;
        //   that happens in PR 2
        ring_data_fd = header->data_fd;
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

    return 0;

Error:
    monad_event_ring_unmap(event_ring);
    return rc;
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

char const *monad_event_ring_get_last_error()
{
    return g_error_buf;
}
