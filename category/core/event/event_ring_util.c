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
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#include <zstd.h>

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

static int decompress_snapshot(
    void const *input_base, size_t input_size, int decompfd, size_t max_size,
    char const *error_name, bool *is_snapshot)
{
    int rc;
    ZSTD_DStream *zds = nullptr;
    size_t zstd_rc = 0;
    uint64_t n_blocks = 0;
    size_t decomp_size = 0;

    *is_snapshot = false;
    size_t const out_buf_size = ZSTD_DStreamOutSize();
    void *const out_buf = malloc(out_buf_size);
    if (out_buf == nullptr) {
        rc = FORMAT_ERRC(errno, "malloc of %zu for zstd failed", out_buf_size);
        goto Done;
    }

    zds = ZSTD_createDStream();
    if (zds == nullptr) {
        rc = FORMAT_ERRC(EIO, "ZSTD_createDStream failed");
        goto Done;
    }

    ZSTD_inBuffer zbuf_in = {.src = input_base, .size = input_size, .pos = 0};

    while (zbuf_in.pos < zbuf_in.size) {
        ZSTD_outBuffer zbuf_out = {
            .dst = out_buf, .size = out_buf_size, .pos = 0};
        zstd_rc = ZSTD_decompressStream(zds, &zbuf_out, &zbuf_in);
        if (ZSTD_isError(zstd_rc)) {
            rc = FORMAT_ERRC(
                EIO,
                "zstd error decompressing `%s`: %s",
                error_name,
                ZSTD_getErrorName(zstd_rc));
            goto Done;
        }
        if (n_blocks++ == 0) {
            // This is the first decompressed block, check if we have the event
            // ring magic number otherwise this is some other kind of zstd file
            if (zbuf_out.pos < sizeof MONAD_EVENT_RING_HEADER_VERSION ||
                memcmp(
                    out_buf,
                    MONAD_EVENT_RING_HEADER_VERSION,
                    sizeof MONAD_EVENT_RING_HEADER_VERSION) != 0) {
                rc = FORMAT_ERRC(
                    EPROTO,
                    "zstd-compressed file `%s` does not contain current magic "
                    "number",
                    error_name);
                goto Done;
            }
            *is_snapshot = true;
        }
        decomp_size += zbuf_out.pos;
        if (max_size != MONAD_EVENT_NO_MAX_SIZE && decomp_size > max_size) {
            rc = FORMAT_ERRC(
                ENOBUFS,
                "decompressed size of `%s` larger than max allowed %zu",
                error_name,
                max_size);
            goto Done;
        }

        uint8_t const *write_buf = zbuf_out.dst;
        size_t residual = zbuf_out.pos;
        while (residual > 0) {
            ssize_t const n_write = write(decompfd, write_buf, residual);
            if (n_write == -1) {
                rc = FORMAT_ERRC(
                    errno,
                    "write of %zd bytes of decompressed `%s` failed",
                    residual,
                    error_name);
                goto Done;
            }
            write_buf += (size_t)n_write;
            residual -= (size_t)n_write;
        }
    }
    if (zstd_rc != 0) {
        // We define a "zstd file" to be a file containing a single compressed
        // frame
        rc = FORMAT_ERRC(
            EPROTO,
            "`%s` appears to contain more than one zstd frame",
            error_name);
        goto Done;
    }
    rc = 0;

Done:
    ZSTD_freeDStream(zds);
    free(out_buf);
    return rc;
}

// Output of the decompress_snap_{buf,fd}_to_temp_file functions; this returns
// the descriptor to the temporary file holding the decompressed contents and
// indicates whether it was a snapshot or not; is_snapshot is indicated
// separately because the routine to check if it's a snapshot decompresses
// the first zstd block so it can check the event ring header, then it stops.
// This will appear as an "exceeded maximum size" error (ENOBUFS), and will
// close the fd and set it to -1; is_snapshot is used to "remember" that it
// _was_ a snapshot, even though the decompression aborted early
struct decompress_output
{
    int fd;
    bool is_snapshot;
};

static int decompress_snap_buf_to_temp_file(
    void const *buf, size_t buf_size, size_t max_size, char const *error_name,
    struct decompress_output *out)
{
    int rc;
    char error_name_buf[64];
    uint32_t magic = 0;

    out->fd = -1;
    out->is_snapshot = false;
    if (error_name == nullptr) {
        sprintf(error_name_buf, "<unknown> buf:%p", buf);
        error_name = error_name_buf;
    }
    memcpy(&magic, buf, buf_size < sizeof(magic) ? buf_size : sizeof(magic));
    if (magic != ZSTD_MAGICNUMBER) {
        // Not a file holding a ZSTD frame
        rc = FORMAT_ERRC(
            EPROTO,
            "snapshot file `%s` does not contain a zstd frame",
            error_name);
        goto Done;
    }

    out->fd = memfd_create("zstd-ring-decomp", 0);
    if (out->fd == -1) {
        rc = FORMAT_ERRC(errno, "could not memfd_create decompression buffer");
        goto Done;
    }
    rc = decompress_snapshot(
        buf, buf_size, out->fd, max_size, error_name, &out->is_snapshot);

Done:
    if (rc != 0) {
        (void)close(out->fd);
        out->fd = -1;
    }
    return rc;
}

static int decompress_snap_fd_to_temp_file(
    int fd_in, size_t max_size, char const *error_name,
    struct decompress_output *out)
{
    int rc;
    struct stat file_stat;
    char error_name_buf[64];

    out->fd = -1;
    out->is_snapshot = false;
    if (error_name == nullptr) {
        sprintf(error_name_buf, "<unknown> fd:%d", fd_in);
        error_name = error_name_buf;
    }

    // Determine the file's size, mmap it into our address space, delegate to
    // decompress_snap_buf_to_temp_file to do most of the work
    if (fstat(fd_in, &file_stat) == -1) {
        return FORMAT_ERRC(errno, "stat of input file `%s` failed", error_name);
    }
    if ((file_stat.st_mode & S_IFREG) == 0 || file_stat.st_size == 0) {
        // Not a regular file we can mmap; map this to EPROTO, our code for
        // "this is not an event ring snapshot"
        return FORMAT_ERRC(
            EPROTO, "`%s` is not an event ring snapshot", error_name);
    }
    size_t const input_size = (size_t)file_stat.st_size;
    void const *const input_base =
        mmap(nullptr, input_size, PROT_READ, MAP_SHARED, fd_in, 0);
    if (input_base == MAP_FAILED) {
        return FORMAT_ERRC(
            errno, "mmap of file `%s` contents failed", error_name);
    }
    rc = decompress_snap_buf_to_temp_file(
        input_base, input_size, max_size, error_name, out);
    (void)munmap((void *)input_base, input_size);
    return rc;
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

int monad_event_is_snapshot_file(
    int fd, char const *error_name, bool *is_snapshot)
{
    struct decompress_output out;
    if (is_snapshot == nullptr) {
        return FORMAT_ERRC(EINVAL, "is_snapshot cannot be nullptr");
    }
    // Decompress the fd as if by monad_event_decompress_snapshot_fd, but with
    // the maximum decompressed size set to the event ring header length; this
    // makes the API fast to call, even for huge files, because it will only
    // decompress a small amount of the file
    *is_snapshot = false;
    int const rc = decompress_snap_fd_to_temp_file(
        fd, sizeof MONAD_EVENT_RING_HEADER_VERSION, error_name, &out);
    (void)close(out.fd);
    // Don't return an error on EPROTO or ENOBUFS; EPROTO just means it's not
    // an event ring file, which is indicated as "success" (rc == 0) and setting
    // *is_snapshot == false; ENOBUFS is expected because the event ring is
    // usually larger than the small `max_size` we passed. Anything else is a
    // genuine error in determining if it was a snapshot or not
    if (rc != 0 && rc != EPROTO && rc != ENOBUFS) {
        return rc;
    }
    *is_snapshot = out.is_snapshot;
    return 0;
}

int monad_event_decompress_snapshot_fd(
    int fd_in, size_t max_size, char const *error_name, int *fd_out)
{
    struct decompress_output out;
    if (fd_out == nullptr) {
        return FORMAT_ERRC(EINVAL, "fd_out cannot be nullptr");
    }
    *fd_out = -1;
    int const rc =
        decompress_snap_fd_to_temp_file(fd_in, max_size, error_name, &out);
    *fd_out = out.fd;
    return rc;
}

int monad_event_decompress_snapshot_mem(
    void const *buf, size_t buf_size, size_t max_size, char const *error_name,
    int *fd_out)
{
    struct decompress_output out;
    if (fd_out == nullptr) {
        return FORMAT_ERRC(EINVAL, "fd_out cannot be nullptr");
    }
    *fd_out = -1;
    int const rc = decompress_snap_buf_to_temp_file(
        buf, buf_size, max_size, error_name, &out);
    *fd_out = out.fd;
    return rc;
}
