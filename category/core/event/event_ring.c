// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <errno.h>
#include <stdbit.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <category/core/event/event_iterator.h>
#include <category/core/event/event_recorder.h>
#include <category/core/event/event_ring.h>
#include <category/core/format_err.h>
#include <category/core/srcloc.h>

thread_local char _g_monad_event_ring_error_buf[1024];
static size_t const PAGE_2MB = 1UL << 21, HEADER_SIZE = PAGE_2MB;

#define FORMAT_ERRC(...)                                                       \
    monad_format_err(                                                          \
        _g_monad_event_ring_error_buf,                                         \
        sizeof(_g_monad_event_ring_error_buf),                                 \
        &MONAD_SOURCE_LOCATION_CURRENT(),                                      \
        __VA_ARGS__)

int monad_event_ring_init_size(
    uint8_t descriptors_shift, uint8_t payload_buf_shift,
    uint16_t context_large_pages, struct monad_event_ring_size *size)
{
    // Do some basic input validation of the size; our main goal here is to
    // protect the event ring from being too small as it can create certain
    // problems (e.g., the descriptor array extent being smaller than a single
    // large page, or problems with the buffer_window_start optimization if
    // WINDOW_INCR is too close in size to the shift, etc.).  While we are
    // here anyway, add some reasonable realistic maximums.
    if (descriptors_shift < MONAD_EVENT_MIN_DESCRIPTORS_SHIFT ||
        descriptors_shift > MONAD_EVENT_MAX_DESCRIPTORS_SHIFT) {
        return FORMAT_ERRC(
            ERANGE,
            "descriptors_shift %hhu outside allowed range [%hhu, %hhu]: "
            "(ring sizes: [%lu, %lu])",
            descriptors_shift,
            MONAD_EVENT_MIN_DESCRIPTORS_SHIFT,
            MONAD_EVENT_MAX_DESCRIPTORS_SHIFT,
            (1UL << MONAD_EVENT_MIN_DESCRIPTORS_SHIFT),
            (1UL << MONAD_EVENT_MAX_DESCRIPTORS_SHIFT));
    }
    if (payload_buf_shift < MONAD_EVENT_MIN_PAYLOAD_BUF_SHIFT ||
        payload_buf_shift > MONAD_EVENT_MAX_PAYLOAD_BUF_SHIFT) {
        return FORMAT_ERRC(
            ERANGE,
            "payload_buf_shift %hhu outside allowed range [%hhu, %hhu]: "
            "(buffer sizes: [%lu, %lu])",
            payload_buf_shift,
            MONAD_EVENT_MIN_PAYLOAD_BUF_SHIFT,
            MONAD_EVENT_MAX_PAYLOAD_BUF_SHIFT,
            (1UL << MONAD_EVENT_MIN_PAYLOAD_BUF_SHIFT),
            (1UL << MONAD_EVENT_MAX_PAYLOAD_BUF_SHIFT));
    }
    size->descriptor_capacity = 1UL << descriptors_shift;
    size->payload_buf_size = 1UL << payload_buf_shift;
    size->context_area_size = PAGE_2MB * context_large_pages;
    return 0;
}

size_t
monad_event_ring_calc_storage(struct monad_event_ring_size const *ring_size)
{
    return PAGE_2MB +
           ring_size->descriptor_capacity *
               sizeof(struct monad_event_descriptor) +
           ring_size->payload_buf_size + ring_size->context_area_size;
}

// A normal event ring is divided into sections, which are aligned to 2 MiB
// x64 large page boundaries:
//
//  .------------------.
//  |   Ring header    |
//  .------------------.
//  | Descriptor array |
//  .------------------.
//  |  Payload buffer  |
//  .------------------.
//  |   Context area   |
//  .------------------.
int monad_event_ring_init_file(
    struct monad_event_ring_size const *ring_size,
    enum monad_event_content_type content_type, uint8_t const *schema_hash,
    int ring_fd, off_t ring_offset, char const *error_name)
{
    size_t ring_bytes;
    void *map_base;
    struct stat ring_stat;
    struct monad_event_ring_header header;
    char namebuf[64];

    if (error_name == nullptr) {
        snprintf(namebuf, sizeof namebuf, "fd:%d [%d]", ring_fd, getpid());
        error_name = namebuf;
    }

    // Do some basic input validation if they didn't obtain their size object
    // via a call to monad_event_ring_init_size
    if (!stdc_has_single_bit(ring_size->descriptor_capacity) ||
        ring_size->descriptor_capacity <
            (1UL << MONAD_EVENT_MIN_DESCRIPTORS_SHIFT) ||
        ring_size->descriptor_capacity >
            (1UL << MONAD_EVENT_MAX_DESCRIPTORS_SHIFT)) {
        return FORMAT_ERRC(
            EINVAL,
            "event ring file `%s` descriptor size %lu is invalid; use "
            "monad_event_ring_init_size",
            error_name,
            ring_size->descriptor_capacity);
    }
    if (!stdc_has_single_bit(ring_size->payload_buf_size) ||
        ring_size->payload_buf_size <
            (1UL << MONAD_EVENT_MIN_PAYLOAD_BUF_SHIFT) ||
        ring_size->payload_buf_size >
            (1UL << MONAD_EVENT_MAX_PAYLOAD_BUF_SHIFT)) {
        return FORMAT_ERRC(
            EINVAL,
            "event ring file `%s` descriptor size %lu is invalid; use "
            "monad_event_ring_init_size",
            error_name,
            ring_size->payload_buf_size);
    }
    if (ring_size->context_area_size > 0 &&
        !stdc_has_single_bit(ring_size->context_area_size)) {
        return FORMAT_ERRC(
            EINVAL,
            "event ring file `%s` context area size %lu is invalid",
            error_name,
            ring_size->context_area_size);
    }
    if (content_type == MONAD_EVENT_CONTENT_TYPE_NONE ||
        content_type >= MONAD_EVENT_CONTENT_TYPE_COUNT) {
        return FORMAT_ERRC(
            EINVAL,
            "event ring file `%s` has invalid content type code %hu",
            error_name,
            content_type);
    }

    memset(&header, 0, sizeof header);
    memcpy(header.magic, MONAD_EVENT_RING_HEADER_VERSION, sizeof header.magic);
    memcpy(header.schema_hash, schema_hash, sizeof header.schema_hash);
    header.content_type = content_type;
    header.size = *ring_size;
    ring_bytes = monad_event_ring_calc_storage(ring_size);

    // The caller is responsible for ensuring that the file range
    // [ring_offset, ring_offset+ring_bytes) is valid. We check that they've
    // done this, because we will mmap this range and need to be sure we won't
    // get SIGBUS upon access.
    if (fstat(ring_fd, &ring_stat) == -1) {
        return FORMAT_ERRC(
            errno, "unable to fstat event ring file `%s`", error_name);
    }
    if (ring_offset + (off_t)sizeof header > ring_stat.st_size) {
        return FORMAT_ERRC(
            ENOSPC,
            "event ring file `%s` cannot hold total event ring size %lu",
            error_name,
            ring_bytes);
    }

    // Map the file and copy the header into it
    map_base =
        mmap(nullptr, ring_bytes, PROT_WRITE, MAP_SHARED, ring_fd, ring_offset);
    if (map_base == MAP_FAILED) {
        return FORMAT_ERRC(
            errno, "mmap failed for event ring file `%s`", error_name);
    }
    memcpy(map_base, &header, sizeof header);

    // To function correctly, all event descriptor's sequence number fields
    // need to be zero'ed out when creating a new event ring. Because we may
    // be given a file region that's already been used, memset the whole
    // descriptor region to zero.
    memset(
        (uint8_t *)map_base + HEADER_SIZE,
        0,
        sizeof(struct monad_event_descriptor) *
            header.size.descriptor_capacity);

    munmap(map_base, ring_bytes);
    return 0;
}

int monad_event_ring_mmap(
    struct monad_event_ring *event_ring, int mmap_prot, int mmap_extra_flags,
    int ring_fd, off_t ring_offset, char const *error_name)
{
    int rc;
    char namebuf[64];
    struct monad_event_ring_header const *header;
    off_t const base_ring_data_offset = ring_offset + (off_t)PAGE_2MB;

    if (event_ring == nullptr) {
        return FORMAT_ERRC(EFAULT, "event_ring cannot be nullptr");
    }
    if (error_name == nullptr) {
        snprintf(namebuf, sizeof namebuf, "fd:%d [%d]", ring_fd, getpid());
        error_name = namebuf;
    }

    event_ring->mmap_prot = mmap_prot;
    header = event_ring->header = mmap(
        nullptr,
        HEADER_SIZE,
        mmap_prot,
        MAP_SHARED | mmap_extra_flags,
        ring_fd,
        ring_offset);
    if (header == MAP_FAILED) {
        return FORMAT_ERRC(
            errno, "mmap of event ring file `%s` header failed", error_name);
    }
    if (memcmp(
            header->magic,
            MONAD_EVENT_RING_HEADER_VERSION,
            sizeof header->magic) != 0) {
        return FORMAT_ERRC(
            EPROTO,
            "event ring file `%s` does not contain current magic number",
            error_name);
    }
    event_ring->desc_capacity_mask =
        event_ring->header->size.descriptor_capacity - 1;
    event_ring->payload_buf_mask =
        event_ring->header->size.payload_buf_size - 1;

    // Map the ring descriptor array from the ring fd
    size_t const descriptor_map_len = header->size.descriptor_capacity *
                                      sizeof(struct monad_event_descriptor);
    event_ring->descriptors = mmap(
        nullptr,
        descriptor_map_len,
        mmap_prot,
        MAP_SHARED | mmap_extra_flags,
        ring_fd,
        base_ring_data_offset);
    if (event_ring->descriptors == MAP_FAILED) {
        rc = FORMAT_ERRC(
            errno,
            "mmap of event ring file `%s` event descriptor array failed",
            error_name);
        goto Error;
    }

    // The mmap step of the payload buffer is more complex: first, reserve a
    // single anonymous mapping whose size is twice the size of the payload
    // buffer, so we can do the "wrap around" trick. We'll remap the actual
    // payload buffer fd into this reserved range later, using MAP_FIXED.
    event_ring->payload_buf = mmap(
        nullptr,
        2 * header->size.payload_buf_size,
        mmap_prot,
        MAP_SHARED | MAP_ANONYMOUS | mmap_extra_flags,
        -1,
        base_ring_data_offset + (off_t)descriptor_map_len);
    if (event_ring->payload_buf == MAP_FAILED) {
        rc = FORMAT_ERRC(
            errno,
            "mmap of event ring file `%s` payload buffer anonymous region "
            "failed",
            error_name);
        goto Error;
    }

    // Map the payload buffer into the first part of the space we just reserved
    if (mmap(
            event_ring->payload_buf,
            header->size.payload_buf_size,
            mmap_prot,
            MAP_FIXED | MAP_SHARED | mmap_extra_flags,
            ring_fd,
            base_ring_data_offset + (off_t)descriptor_map_len) == MAP_FAILED) {
        rc = FORMAT_ERRC(
            errno,
            "fixed mmap of event ring file `%s` payload buffer to %p failed",
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
            event_ring->payload_buf + header->size.payload_buf_size,
            header->size.payload_buf_size,
            mmap_prot,
            MAP_FIXED | MAP_SHARED | mmap_extra_flags,
            ring_fd,
            base_ring_data_offset + (off_t)descriptor_map_len) == MAP_FAILED) {
        rc = FORMAT_ERRC(
            errno,
            "fixed mmap of event ring file `%s` payload buffer wrap-around "
            "pages at %p "
            "failed",
            error_name,
            event_ring->payload_buf + header->size.payload_buf_size);
        goto Error;
    }

    if (header->size.context_area_size > 0) {
        event_ring->context_area = mmap(
            nullptr,
            header->size.context_area_size,
            mmap_prot,
            MAP_SHARED | mmap_extra_flags,
            ring_fd,
            base_ring_data_offset +
                (off_t)(descriptor_map_len + header->size.payload_buf_size));
        if (event_ring->context_area == MAP_FAILED) {
            rc = FORMAT_ERRC(
                errno,
                "mmap of event ring file `%s` context area failed",
                error_name);
            goto Error;
        }
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
                header->size.descriptor_capacity *
                    sizeof(struct monad_event_descriptor));
        }
        if (event_ring->payload_buf) {
            munmap(event_ring->payload_buf, 2 * header->size.payload_buf_size);
        }
        if (event_ring->context_area) {
            munmap(event_ring->context_area, header->size.context_area_size);
        }
        munmap((void *)header, HEADER_SIZE);
    }
    memset(event_ring, 0, sizeof *event_ring);
}

int monad_event_ring_init_iterator(
    struct monad_event_ring const *event_ring,
    struct monad_event_iterator *iter)
{
    memset(iter, 0, sizeof *iter);
    struct monad_event_ring_header const *header = event_ring->header;
    if (header == nullptr) {
        return FORMAT_ERRC(EINVAL, "event_ring has been unmapped");
    }
    if ((event_ring->mmap_prot & PROT_READ) == 0) {
        return FORMAT_ERRC(EACCES, "event_ring memory not mapped for reading");
    }
    iter->descriptors = event_ring->descriptors;
    iter->desc_capacity_mask = header->size.descriptor_capacity - 1;
    iter->control = &header->control;
    (void)monad_event_iterator_reset(iter);
    return 0;
}

int monad_event_ring_init_recorder(
    struct monad_event_ring const *event_ring,
    struct monad_event_recorder *recorder)
{
    memset(recorder, 0, sizeof *recorder);
    struct monad_event_ring_header *header = event_ring->header;
    if (header == nullptr) {
        return FORMAT_ERRC(EINVAL, "event_ring has been unmapped");
    }
    if ((event_ring->mmap_prot & PROT_WRITE) == 0) {
        return FORMAT_ERRC(EACCES, "event_ring memory not mapped for writing");
    }
    recorder->descriptors = event_ring->descriptors;
    recorder->payload_buf = event_ring->payload_buf;
    recorder->control = &header->control;
    recorder->desc_capacity_mask = header->size.descriptor_capacity - 1;
    recorder->payload_buf_mask = header->size.payload_buf_size - 1;
    return 0;
}

char const *monad_event_ring_get_last_error()
{
    return _g_monad_event_ring_error_buf;
}

char const *g_monad_event_content_type_names[MONAD_EVENT_CONTENT_TYPE_COUNT] = {
    [MONAD_EVENT_CONTENT_TYPE_NONE] = "none",
    [MONAD_EVENT_CONTENT_TYPE_TEST] = "test",
    [MONAD_EVENT_CONTENT_TYPE_EXEC] = "exec",
};
