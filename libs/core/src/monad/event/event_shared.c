#include <errno.h>
#include <stdarg.h>
#include <stdbit.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include <sys/mman.h>
#include <unistd.h>

#include <monad/core/assert.h>
#include <monad/core/srcloc.h>
#include <monad/event/event.h>
#include <monad/event/event_shared.h>

static size_t const PAGE_2MB = (1UL << 21); // x64 2MiB large page

static char const *final_path_component(char const *path)
{
    char const *f = path + strlen(path);
    while (f != path && *f != '/') {
        --f;
    }
    return *f == '/' ? f + 1 : path;
}

extern int _monad_event_vformat_err(
    char *error_buf, size_t size, monad_source_location_t const *srcloc,
    int err, char const *format, va_list ap)
{
    size_t len;
    int rc = 0;

    if (srcloc != nullptr) {
        rc = snprintf(
            error_buf,
            size,
            "%s@%s:%u",
            srcloc->function_name,
            final_path_component(srcloc->file_name),
            srcloc->line);
    }
    len = rc > 0 ? (size_t)rc : 0;
    if (len < size - 2) {
        error_buf[len++] = ':';
        error_buf[len++] = ' ';
        rc = vsnprintf(error_buf + len, size - len, format, ap);
        if (rc >= 0) {
            len += (size_t)rc;
        }
    }
    if (err != 0 && len < size) {
        (void)snprintf(
            error_buf + len, size - len, ": %s (%d)", strerror(err), err);
    }
    return err;
}

int _monad_event_mmap_descriptor_table(
    enum monad_event_ring_type ring_type, uint8_t ring_shift,
    char const *ring_id, _monad_event_format_err_fn *err_fn,
    struct monad_event_descriptor **table, size_t *ring_capacity, int *fd)
{
#define ES_ERR(...) (*err_fn)(&MONAD_SOURCE_LOCATION_CURRENT(), __VA_ARGS__)
    size_t desc_table_map_len;
    char name[32];
    int mmap_prot;

    if (ring_type == MONAD_EVENT_RING_TYPE_SHARED) {
        mmap_prot = PROT_WRITE;
    }
    else {
        MONAD_ASSERT(ring_type == MONAD_EVENT_RING_TYPE_RECORDER);
        // Note that even though we don't need to share this ring with external
        // processes, the mmap flags will still contain MAP_SHARED rather than
        // MAP_PRIVATE; if we don't do it that way, the "wrap-around" first
        // page of the descriptor table would be mapped to a separate physical
        // page, defeating the purpose
        mmap_prot = PROT_READ | PROT_WRITE;
    }

    // Map the ring descriptor table; this uses huge pages and also the
    // "wrap-around" technique. If the ring size is too small, we need to
    // round the ring_size up such that it fill an entire 2MB page.
    *ring_capacity = 1UL << ring_shift;
    desc_table_map_len = *ring_capacity * sizeof(struct monad_event_descriptor);
    if (desc_table_map_len < PAGE_2MB) {
        desc_table_map_len = PAGE_2MB;
        *ring_capacity =
            desc_table_map_len / sizeof(struct monad_event_descriptor);
    }
    snprintf(name, sizeof name, "evt_rdt:%s", ring_id);
    *fd = memfd_create(name, MFD_CLOEXEC | MFD_HUGETLB);
    if (*fd == -1) {
        return ES_ERR(errno, "memfd_create(2) failed for %s", name);
    }
    if (ftruncate(*fd, (off_t)desc_table_map_len) == -1) {
        return ES_ERR(errno, "ftruncate(2) failed for %s", name);
    }

    // First, reserve a single anonymous mapping whose size encompasses both
    // the nominal size of the descriptor table plus the size of the
    // wrap-around large page. We'll remap the memfd into this reserved range
    // later, using MAP_FIXED.
    *table = mmap(
        nullptr,
        desc_table_map_len + PAGE_2MB,
        mmap_prot,
        MAP_SHARED | MAP_ANONYMOUS | MAP_HUGETLB,
        -1,
        0);
    if (*table == MAP_FAILED) {
        return ES_ERR(errno, "mmap(2) unable to map %s", name);
    }

    // Map the descriptor table into the first part of the space we just
    // reserved
    if (mmap(
            *table,
            desc_table_map_len,
            mmap_prot,
            MAP_SHARED | MAP_FIXED | MAP_HUGETLB | MAP_POPULATE,
            *fd,
            0) == MAP_FAILED) {
        return ES_ERR(
            errno,
            "unable to remap descriptor table range to memfd for %s",
            name);
    }

    // Map the "wrap around" large page after the descriptor table. This causes
    // the first large page of the table to be mapped immediately after the end
    // of the table, allowing us to naturally "wrap around" in memory by the
    // size of one full large page. Thus we can bulk memcpy(3) event
    // descriptors safely near the end of the table, and it will wrap around
    // in memory without doing any error-prone index massaging.
    if (mmap(
            (uint8_t *)*table + desc_table_map_len,
            PAGE_2MB,
            mmap_prot,
            MAP_SHARED | MAP_FIXED | MAP_HUGETLB | MAP_POPULATE,
            *fd,
            0) == MAP_FAILED) {
        return ES_ERR(errno, "mmap(2) wrap-around mapping for %s failed", name);
    }

    // Despite the MAP_POPULATE, we don't necessarily trust that everything
    // is ready yet; "warm up" the mappings by writing over the entire range
    memset(*table, 0, desc_table_map_len + PAGE_2MB);
    return 0;
}

void _monad_event_unmap_descriptor_table(
    struct monad_event_descriptor *table, size_t ring_capacity)
{
    size_t const desc_table_map_len = ring_capacity * sizeof(table[0]);
    munmap(table, desc_table_map_len);
    munmap((uint8_t *)table + desc_table_map_len, PAGE_2MB);
}
