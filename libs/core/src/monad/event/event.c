#include <errno.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

#include <fcntl.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <unistd.h>

#include <monad/core/format_err.h>
#include <monad/event/event.h>

thread_local char _g_monad_event_error_buf[1024];
static size_t const PAGE_2MB = 1UL << 21;

#define FORMAT_ERRC(...)                                                       \
    monad_format_err(                                                          \
        _g_monad_event_error_buf,                                              \
        sizeof(_g_monad_event_error_buf),                                      \
        &MONAD_SOURCE_LOCATION_CURRENT(),                                      \
        __VA_ARGS__)

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
    struct monad_event_ring *event_ring, int ring_fd, off_t ring_offset,
    char const *error_name)
{
    int rc;
    off_t const base_ring_data_offset = ring_offset + (off_t)PAGE_2MB;
    struct monad_event_ring_header const *const header = event_ring->header;
    int const mmap_prot = PROT_READ | PROT_WRITE;

    // Map the ring descriptor array from the ring fd
    size_t const descriptor_map_len =
        header->descriptor_capacity * sizeof(struct monad_event_descriptor);
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

size_t
monad_event_ring_calculate_size(size_t ring_capacity, size_t payload_buf_size)
{
    return PAGE_2MB + ring_capacity * sizeof(struct monad_event_descriptor) +
           payload_buf_size;
}

void monad_event_ring_unmap(struct monad_event_ring *event_ring)
{
    struct monad_event_ring_header const *const header = event_ring->header;
    if (header != nullptr) {
        if (event_ring->descriptors) {
            munmap(
                event_ring->descriptors,
                header->descriptor_capacity *
                    sizeof(struct monad_event_descriptor));
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
