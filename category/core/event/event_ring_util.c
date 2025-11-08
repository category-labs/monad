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
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <fcntl.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <sys/types.h>

#if __has_include(<linux/limits.h>)
    #include <linux/limits.h> // NOLINT(misc-include-cleaner)
#else
    #define PATH_MAX 4096
#endif

#include <category/core/event/event_ring.h>
#include <category/core/event/event_ring_util.h>
#include <category/core/format_err.h>
#include <category/core/path_util.h>
#include <category/core/srcloc.h>

#if !MONAD_EVENT_DISABLE_LIBHUGETLBFS
    #include <category/core/mem/hugetlb_path.h>
#endif

// Defined in event_ring.c, so we can share monad_event_ring_get_last_error()
extern thread_local char _g_monad_event_ring_error_buf[1024];

#define FORMAT_ERRC(...)                                                       \
    monad_format_err(                                                          \
        _g_monad_event_ring_error_buf,                                         \
        sizeof(_g_monad_event_ring_error_buf),                                 \
        &MONAD_SOURCE_LOCATION_CURRENT(),                                      \
        __VA_ARGS__)

// Create MONAD_EVENT_DEFAULT_RING_DIR or override subpaths with rwxrwxr-x
constexpr mode_t DIR_CREATE_MODE = S_IRWXU | S_IRWXG | S_IROTH | S_IXOTH;

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
    rc = posix_fallocate(ring_fd, ring_offset, (off_t)ring_bytes);
    if (rc != 0) {
        return FORMAT_ERRC(
            rc,
            "posix_fallocate failed for event ring file `%s`, size %lu",
            error_name,
            ring_bytes);
    }
    return monad_event_ring_init_file(
        &ring_size,
        ring_config->content_type,
        ring_config->schema_hash,
        ring_fd,
        ring_offset,
        error_name);
}

int monad_event_ring_check_content_type(
    struct monad_event_ring const *event_ring,
    enum monad_event_content_type content_type, uint8_t const *schema_hash)
{
    if (event_ring == nullptr || event_ring->header == nullptr) {
        return FORMAT_ERRC(EFAULT, "event ring is not mapped");
    }
    if (event_ring->header->content_type != content_type) {
        return FORMAT_ERRC(
            EPROTO,
            "required event ring content type is %hu, file contains %hu",
            content_type,
            event_ring->header->content_type);
    }
    if (memcmp(
            event_ring->header->schema_hash,
            schema_hash,
            sizeof event_ring->header->schema_hash) != 0) {
        return FORMAT_ERRC(EPROTO, "event ring schema hash does not match");
    }
    return 0;
}

int monad_event_ring_query_excl_writer_pid(int ring_fd, pid_t *pid)
{
    int rc;
    struct monad_event_flock_info fl_info;
    size_t lock_count = 1;

    *pid = 0;
    rc = monad_event_ring_query_flocks(ring_fd, &fl_info, &lock_count);
    if (rc != 0) {
        return rc;
    }
    *pid = lock_count == 1 && fl_info.lock == LOCK_EX ? fl_info.pid : 0;
    if (*pid == 0) {
        return FORMAT_ERRC(EOWNERDEAD, "no exclusive writer process found");
    }
    return 0;
}

// libhugetlbfs is always present for Category Labs, but when this is compiled
// by third parties using the SDK, it is optional
#if MONAD_EVENT_DISABLE_LIBHUGETLBFS

int monad_event_open_hugetlbfs_dir_fd(int *, char *, size_t)
{
    return FORMAT_ERRC(ENOSYS, "compiled without libhugetlbfs support");
}

#else

int monad_event_open_hugetlbfs_dir_fd(
    int *dirfd, char *pathbuf, size_t pathbuf_size)
{
    struct monad_hugetlbfs_resolve_params const params = {
        .page_size = 1UL << 21,
        .path_suffix = MONAD_EVENT_DEFAULT_RING_DIR,
        .create_dirs = true,
        .dir_create_mode = DIR_CREATE_MODE};
    int const rc =
        monad_hugetlbfs_open_dir_fd(&params, dirfd, pathbuf, pathbuf_size);
    if (rc != 0) {
        // Copy the error message directly, since we added nothing interesting
        strlcpy(
            _g_monad_event_ring_error_buf,
            monad_hugetlbfs_get_last_error(),
            sizeof _g_monad_event_ring_error_buf);
    }
    return rc;
}

#endif

int monad_event_resolve_ring_file(
    char const *default_path, char const *file, char *pathbuf,
    size_t pathbuf_size)
{
    int rc;

    if (file == nullptr || pathbuf == nullptr) {
        return FORMAT_ERRC(EFAULT, "file and pathbuf cannot be nullptr");
    }
    if (file == pathbuf) {
        return FORMAT_ERRC(EINVAL, "file cannot alias pathbuf");
    }
    if (strchr(file, '/') != nullptr) {
        // The event ring file contains a '/' character; this is resolved
        // relative to the current working directory
        if (strlcpy(pathbuf, file, pathbuf_size) >= pathbuf_size) {
            return FORMAT_ERRC(
                ENAMETOOLONG,
                "file %s overflows %zu size pathbuf",
                file,
                pathbuf_size);
        }
        return 0;
    }

    // The event ring path does not contain a '/'; we assume this is a file
    // name relative to the default event ring directory
    if (default_path == MONAD_EVENT_DEFAULT_HUGETLBFS) {
        rc = monad_event_open_hugetlbfs_dir_fd(nullptr, pathbuf, pathbuf_size);
        if (rc != 0) {
            return rc;
        }
    }
    else {
        rc = monad_path_open_subdir(
            AT_FDCWD,
            default_path,
            DIR_CREATE_MODE,
            nullptr,
            pathbuf,
            pathbuf_size);
        if (rc != 0) {
            return FORMAT_ERRC(
                rc,
                "monad_path_open_subdir of `%s` failed at `%s`",
                default_path,
                pathbuf);
        }
    }

    size_t const default_dir_len = strlen(pathbuf);
    char *append = pathbuf + default_dir_len;
    pathbuf_size -= default_dir_len;
    rc = monad_path_append(&append, file, &pathbuf_size);
    if (rc != 0) {
        return FORMAT_ERRC(
            rc, "monad_path_append of %s failed; partial: %s", file, pathbuf);
    }

    return 0;
}
