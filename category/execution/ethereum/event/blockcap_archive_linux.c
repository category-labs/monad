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
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>

#include <category/core/event/evcap_writer.h>
#include <category/core/format_err.h>
#include <category/core/srcloc.h>
#include <category/execution/ethereum/event/blockcap.h>

// Defined in blockcap_builder.c
extern thread_local char _g_monad_bcap_error_buf[1024];

#define FORMAT_ERRC(...)                                                       \
    monad_format_err(                                                          \
        _g_monad_bcap_error_buf,                                               \
        sizeof(_g_monad_bcap_error_buf),                                       \
        &MONAD_SOURCE_LOCATION_CURRENT(),                                      \
        __VA_ARGS__)

int monad_bcap_archive_open_block_fd(
    struct monad_bcap_archive const *bca, uint64_t const block_number,
    int const open_flags, mode_t const dir_create_mode,
    mode_t const file_create_mode, char *path_buf, size_t path_buf_size,
    int *const fd_out)
{
    char subdir_buf[32];
    char const *subdir_end;
    char local_path_buf[64];
    int dirfd;
    int fd;
    int rc;

    if (fd_out != nullptr) {
        *fd_out = -1;
    }
    if (path_buf == nullptr) {
        path_buf = local_path_buf;
        path_buf_size = sizeof local_path_buf;
    }

    dirfd = monad_bcap_archive_get_dirfd(bca);
    rc = monad_bcap_archive_format_block_path(
        block_number, path_buf, path_buf_size, &subdir_end);
    if (rc != 0) {
        return rc;
    }
    *(char *)mempcpy(subdir_buf, path_buf, (size_t)(subdir_end - path_buf)) =
        '\0';
    if (open_flags & (O_CREAT | O_TMPFILE)) {
        // We're allowed to create the file; we'll try to create the group
        // directory
        if (mkdirat(dirfd, subdir_buf, dir_create_mode) == -1 &&
            errno != EEXIST) {
            return FORMAT_ERRC(
                errno,
                "unable to create directory %s to write block %lu",
                subdir_buf,
                block_number);
        }
    }
    fd = openat(
        dirfd,
        open_flags & O_TMPFILE ? subdir_buf : path_buf,
        open_flags,
        file_create_mode);
    if (fd == -1) {
        return FORMAT_ERRC(
            errno, "could not open %s [block %lu]", path_buf, block_number);
    }
    if (fd_out != nullptr) {
        *fd_out = fd;
    }
    else {
        (void)close(fd);
    }
    return 0;
}

int monad_bcap_archive_close_block_writer(
    struct monad_bcap_archive *bca, uint64_t block_number,
    struct monad_evcap_writer *evcap_writer, char const *path_buf)
{
    char local_path_buf[64];
    int rc;
    int const dirfd = monad_bcap_archive_get_dirfd(bca);
    int const block_fd = monad_evcap_writer_get_fd(evcap_writer);
    if (path_buf == nullptr) {
        rc = monad_bcap_archive_format_block_path(
            block_number, local_path_buf, sizeof local_path_buf, nullptr);
        if (rc != 0) {
            return rc;
        }
        path_buf = local_path_buf;
    }
    rc = 0;
    if (linkat(block_fd, "", dirfd, path_buf, AT_EMPTY_PATH) == -1) {
        rc = FORMAT_ERRC(
            errno,
            "could not link block file %lu into the filesystem at %s",
            block_number,
            path_buf);
    }
    monad_evcap_writer_destroy(evcap_writer);
    return rc;
}
