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

#include <category/core/cleanup.h> // NOLINT(misc-include-cleaner)
#include <category/core/format_err.h>
#include <category/core/mem/hugetlb_path.h>
#include <category/core/path_util.h>
#include <category/core/srcloc.h>

#include <hugetlbfs.h>

#include <errno.h>
#include <stddef.h>
#include <string.h>

#include <fcntl.h>
#include <linux/limits.h>

thread_local char g_error_buf[PATH_MAX];

#define FORMAT_ERRC(...)                                                       \
    monad_format_err(                                                          \
        g_error_buf,                                                           \
        sizeof g_error_buf,                                                    \
        &MONAD_SOURCE_LOCATION_CURRENT(),                                      \
        __VA_ARGS__)

int monad_hugetlbfs_open_dir_fd(
    struct monad_hugetlbfs_resolve_params const *params, int *dirfd,
    char *pathbuf, size_t pathbuf_size)
{
    size_t resolve_size;
    char const *hugetlbfs_mount_path;
    char local_pathbuf[PATH_MAX];
#ifdef O_PATH
    constexpr int OPEN_FLAGS = O_DIRECTORY | O_PATH;
#else
    constexpr int OPEN_FLAGS = O_DIRECTORY;
#endif

    if (params == nullptr) {
        return FORMAT_ERRC(EFAULT, "params cannot be nullptr");
    }
    if (pathbuf == nullptr) {
        // Even if the user doesn't want the full absolute path, we need it
        // locally for better error reporting
        pathbuf = local_pathbuf;
        pathbuf_size = sizeof local_pathbuf;
    }
    if (params->page_size == 0) {
        long default_size = gethugepagesize();
        if (default_size == -1) {
            return FORMAT_ERRC(errno, "no default huge page size configured");
        }
        resolve_size = (size_t)default_size;
    }
    else {
        resolve_size = params->page_size;
    }
    hugetlbfs_mount_path = hugetlbfs_find_path_for_size((long)resolve_size);
    if (hugetlbfs_mount_path == nullptr) {
        return FORMAT_ERRC(
            ENODEV, "no mounted hugetlbfs is accessible to this user");
    }
    size_t const mount_path_len =
        strlcpy(pathbuf, hugetlbfs_mount_path, pathbuf_size);
    if (mount_path_len >= pathbuf_size) {
        return FORMAT_ERRC(
            ENAMETOOLONG, "pathbuf cannot hold %s", hugetlbfs_mount_path);
    }
    int mountfd [[gnu::cleanup(cleanup_close)]] =
        open(hugetlbfs_mount_path, OPEN_FLAGS);
    if (mountfd == -1) {
        return FORMAT_ERRC(
            errno, "open of hugetlbfs mount `%s` failed", hugetlbfs_mount_path);
    }
    int const rc = monad_path_open_subdir(
        mountfd,
        params->path_suffix,
        params->create_dirs ? params->dir_create_mode : MONAD_PATH_NO_CREATE,
        dirfd,
        pathbuf + mount_path_len,
        pathbuf_size - mount_path_len);
    if (rc != 0) {
        return FORMAT_ERRC(
            rc,
            "monad_path_open_subdir of `%s` underneath `%s` failed at last "
            "path component of `%s`",
            params->path_suffix,
            hugetlbfs_mount_path,
            pathbuf);
    }
    return 0;
}

char const *monad_hugetlbfs_get_last_error()
{
    return g_error_buf;
}
