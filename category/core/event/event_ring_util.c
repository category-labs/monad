#include <errno.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#include <fcntl.h>
#include <linux/magic.h>
#include <sys/stat.h>
#include <sys/vfs.h>

#include <category/core/format_err.h>
#include <category/core/event/event_ring.h>
#include <category/core/event/event_ring_util.h>

// Defined in event_ring.c, so we can share monad_event_ring_get_last_error()
extern thread_local char _g_monad_event_ring_error_buf[1024];

#define FORMAT_ERRC(...)                                                       \
    monad_format_err(                                                          \
        _g_monad_event_ring_error_buf,                                         \
        sizeof(_g_monad_event_ring_error_buf),                                 \
        &MONAD_SOURCE_LOCATION_CURRENT(),                                      \
        __VA_ARGS__)

// Given a path which may not exist, walk backward until we find a parent path
// that does exist; the caller must free(3) parent_path
static int find_existing_parent_path(char const *path, char **parent_path)
{
    struct stat path_stat;

    *parent_path = nullptr;
    if (strlen(path) == 0) {
        return FORMAT_ERRC(EINVAL, "path cannot be nullptr or empty");
    }
    *parent_path = strdup(path);

StatAgain:
    if (stat(*parent_path, &path_stat) == -1) {
        if (errno != ENOENT) {
            // stat failed for some reason other than ENOENT; we just give up
            // in this case
            return FORMAT_ERRC(errno, "stat of `%s` failed", *parent_path);
        }

        // For ENOENT failures, climb up the path until we find a path that
        // does exist. If we were given an absolute path, we'll eventually
        // succeed in stat'ing `/` (and thus won't always get ENOENT). If we
        // were given a relative path, we'll eventually run out of `/`
        // characters, in which case the path of interest is assumed to be
        // the current working directory, "."
        char *const last_path_sep = strrchr(*parent_path, '/');
        if (last_path_sep == nullptr) {
            strcpy(*parent_path, ".");
        }
        else {
            *last_path_sep = '\0';
            goto StatAgain;
        }
    }
    return 0;
}

int monad_event_ring_init_simple(
    struct monad_event_ring_simple_config const *ring_config, int ring_fd,
    off_t ring_offset, char const *error_name)
{
    struct monad_event_ring_size ring_size;
    int rc = monad_event_ring_init_size(
        ring_config->descriptors_shift,
        ring_config->payload_buf_shift,
        ring_config->context_large_pages,
        &ring_size);
    if (rc != 0) {
        return rc;
    }
    size_t const ring_bytes = monad_event_ring_calc_storage(&ring_size);
    if (fallocate(ring_fd, 0, ring_offset, (off_t)ring_bytes) == -1) {
        return FORMAT_ERRC(
            errno,
            "fallocate failed for event ring file `%s`, size %lu",
            error_name,
            ring_bytes);
    }
    return monad_event_ring_init_file(
        &ring_size,
        ring_config->ring_type,
        ring_config->metadata_hash,
        ring_fd,
        ring_offset,
        error_name);
}

int monad_event_ring_check_type(
    struct monad_event_ring const *event_ring,
    enum monad_event_ring_type ring_type, uint8_t const *metadata_hash)
{
    if (event_ring == nullptr || event_ring->header == nullptr) {
        return FORMAT_ERRC(EFAULT, "event ring is not mapped");
    }
    if (event_ring->header->type != ring_type) {
        return FORMAT_ERRC(
            EPROTO,
            "required event ring type is %hu, file contains %hu",
            ring_type,
            event_ring->header->type);
    }
    if (memcmp(
            event_ring->header->metadata_hash,
            metadata_hash,
            sizeof event_ring->header->metadata_hash) != 0) {
        return FORMAT_ERRC(EPROTO, "event ring metadata does not match");
    }
    return 0;
}

int monad_event_ring_find_writer_pids(
    int ring_fd, pid_t *pids, size_t *pids_size)
{
    (void)ring_fd, (void)pids, (void)pids_size;
    return FORMAT_ERRC(
        ENOSYS, "implementation deferred to another PR, for length");
}

int monad_check_path_supports_map_hugetlb(char const *path, bool *supported)
{
    char *parent_path;
    struct statfs fs_stat;
    int rc;

    *supported = false;
    rc = find_existing_parent_path(path, &parent_path);
    if (rc != 0) {
        goto Done;
    }
    if (statfs(parent_path, &fs_stat) == -1) {
        rc = FORMAT_ERRC(errno, "statfs of `%s` failed", parent_path);
        goto Done;
    }
    else {
        // Only hugetlbfs supports MAP_HUGETLB
        *supported = fs_stat.f_type == HUGETLBFS_MAGIC;
        rc = 0;
    }
Done:
    free(parent_path);
    return rc;
}
