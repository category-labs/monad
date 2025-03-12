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
#include <stdlib.h>
#include <string.h>

#include <fcntl.h>
#include <limits.h>
#include <sys/stat.h>
#include <unistd.h>

#include <hugetlbfs.h>

#include <category/core/format_err.h>
#include <category/core/srcloc.h>
#include <category/core/mem/hugetlb_path.h>

thread_local char g_error_buf[PATH_MAX];

#define FORMAT_ERRC(...)                                                       \
    monad_format_err(                                                          \
        g_error_buf,                                                           \
        sizeof g_error_buf,                                                    \
        &MONAD_SOURCE_LOCATION_CURRENT(),                                      \
        __VA_ARGS__)

static int
path_append(char **dst, char const *src, size_t *size, bool prepend_sep)
{
    if (*dst == nullptr) {
        return 0;
    }
    if (prepend_sep) {
        if (*size == 0) {
            return FORMAT_ERRC(ERANGE, "path buffer overflow");
        }
        **dst = '/';
        *dst += 1;
        *size -= 1;
    }
    size_t const n = strlcpy(*dst, src, *size);
    if (n >= *size) {
        *dst += *size;
        *size = 0;
        return FORMAT_ERRC(ERANGE, "path buffer overflow");
    }
    *dst += n;
    *size -= n;
    return 0;
}

static int walk_path_suffix(
    char const *path_suffix, bool create_dirs, mode_t mode, int *curfd,
    char const *const namebuf_start, char *namebuf, size_t namebuf_size)
{
    int rc = 0;
    char *dir_name;
    char *tokctx;

    char *path_components = strdup(path_suffix);
    if (path_components == nullptr) {
        return FORMAT_ERRC(errno, "strdup of `%s` failed", path_suffix);
    }

    for (dir_name = strtok_r(path_components, "/", &tokctx); dir_name;
         dir_name = strtok_r(nullptr, "/", &tokctx)) {
        // This loop iterates over the path components in a path string; each
        // path component is the name of a directory.
        //
        // Within this loop, `dir_name` refers to the next path component and
        // `*curfd` is an open file descriptor to the parent directory of
        // `dir_name`; the "walk" involves:
        //
        //   - creating a directory named `dir_name` if it doesn't exist and
        //     we're allowed to create directories
        //
        //   - opening a file descriptor to `dir_name` as the new `*curfd`
        //     with O_DIRECTORY (thereby checking if it is a directory in
        //     case we got EEXIST but it is some other type of file)
        //
        //   - appending the `dir_name` to `namebuf`
        //
        // When we're done, `*curfd` is an open file descriptor to the last
        // directory in the path; if we fail early for any reason, the error
        // will indicate what path component is responsible for the error,
        // e.g., in `/a/b/c/d` if `c` exists but is not a directory we'll get
        // ENOTDIR with the error string indicating that it occured for path
        // component `c` at `/a/b`
        int nextfd, lastfd;
        if (create_dirs && mkdirat(*curfd, dir_name, mode) == -1 &&
            errno != EEXIST) {
            rc = FORMAT_ERRC(
                errno,
                "mkdir of `%s` at path `%s` failed",
                dir_name,
                namebuf_start ? namebuf_start : "<unknown>");
            goto Error;
        }
        nextfd = openat(*curfd, dir_name, O_DIRECTORY | O_PATH);
        if (nextfd == -1) {
            rc = FORMAT_ERRC(
                errno,
                "openat of `%s` at path `%s` failed",
                dir_name,
                namebuf_start ? namebuf_start : "<unknown>");
            goto Error;
        }
        lastfd = *curfd;
        *curfd = nextfd;
        (void)close(lastfd);
        rc = path_append(
            &namebuf, dir_name, &namebuf_size, /*prepend_sep*/ true);
    }
    free(path_components);
    return rc;

Error:
    free(path_components);
    (void)close(*curfd);
    *curfd = -1;
    return rc;
}

int monad_hugetlbfs_open_dir_fd(
    struct monad_hugetlbfs_resolve_params const *params, int *dirfd,
    char *namebuf, size_t namebuf_size)
{
    int rc;
    size_t resolve_size;
    char const *hugetlbfs_mount_path;
    char const *const namebuf_start = namebuf;
    int curfd;

    if (params == nullptr) {
        return FORMAT_ERRC(EFAULT, "params cannot be nullptr");
    }
    if (dirfd != nullptr) {
        // Ensure the caller doesn't accidentally close something (i.e., stdin)
        // if they unconditionally close upon failure
        *dirfd = -1;
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
    rc = path_append(
        &namebuf, hugetlbfs_mount_path, &namebuf_size, /*prepend_sep*/ false);
    curfd = open(hugetlbfs_mount_path, O_DIRECTORY | O_PATH);
    if (curfd == -1) {
        return FORMAT_ERRC(
            errno, "open of hugetlbfs mount `%s` failed", hugetlbfs_mount_path);
    }
    rc = walk_path_suffix(
        params->path_suffix,
        params->create_dirs,
        params->dir_create_mode,
        &curfd,
        namebuf_start,
        namebuf,
        namebuf_size);
    if (dirfd) {
        *dirfd = curfd;
    }
    else {
        (void)close(curfd);
    }
    return rc;
}

char const *monad_hugetlbfs_get_last_error()
{
    return g_error_buf;
}
