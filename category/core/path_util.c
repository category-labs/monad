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
#include <string.h>

#include <fcntl.h>
#include <limits.h>
#include <sys/stat.h>
#include <unistd.h>

#include <category/core/cleanup.h> // NOLINT(misc-include-cleaner)
#include <category/core/path_util.h>

// Silence clang-tidy complaining about trying to close AT_FDCWD
static void tidy_close(int fd)
{
    if (fd >= 0) {
        (void)close(fd);
    }
}

int monad_path_append(char **dst, char const *src, size_t *size)
{
    if (dst == nullptr || src == nullptr || size == nullptr) {
        return EFAULT;
    }
    if (*dst == nullptr) {
        return ENOBUFS;
    }
    if (**dst != '\0') {
        return EINVAL;
    }
    if (*size == 0) {
        return ENAMETOOLONG;
    }
    **dst = '/';
    *dst += 1;
    *size -= 1;
    size_t const n = strlcpy(*dst, src, *size);
    if (n >= *size) {
        *dst += *size;
        *size = 0;
        return ENAMETOOLONG;
    }
    *dst += n;
    *size -= n;
    return 0;
}

int monad_path_open_subdir(
    int const init_dirfd, char const *path_suffix, mode_t mode,
    int *final_dirfd, char *pathbuf, size_t pathbuf_size)
{
    char *dir_name;
    char *tokctx;
    int curfd;
    int rc = 0;
    bool const can_create_dirs = (mode & (S_IRWXU | S_IRWXG | S_IRWXO)) != 0;
#ifdef O_PATH
    constexpr int OPEN_FLAGS = O_DIRECTORY | O_PATH;
#else
    constexpr int OPEN_FLAGS = O_DIRECTORY;
#endif

    if (pathbuf != nullptr) {
        *pathbuf = '\0';
    }
    if (final_dirfd != nullptr) {
        // Ensure the caller doesn't accidentally close something (e.g., stdin)
        // if they don't initialize *final_dirfd, then unconditionally close
        // upon failure
        *final_dirfd = -1;
    }

    if (path_suffix == nullptr) {
        if (final_dirfd != nullptr) {
            *final_dirfd = init_dirfd;
        }
        return 0;
    }

    // Setup curfd
    if (init_dirfd == AT_FDCWD) {
        curfd = AT_FDCWD;
        if (*path_suffix == '/') {
            // Properly support absolute paths with AT_FDCWD; we wouldn't get
            // it right without this special case because we walk relative
            // paths one path component at a time, so e.g., "/tmp/xyz" would
            // accidentally mkdirat <cwd>/tmp on the first iteration
            curfd = open("/", OPEN_FLAGS);
        }
    }
    else {
        // This allows us to unconditionally close the curfd on any path,
        // simplifying the logic
        curfd = dup(init_dirfd);
    }
    if (curfd == -1) {
        return errno; // dup(2) or open(2) error
    }

    // NOLINTBEGIN(clang-analyzer-unix.Malloc)
    char *const path_components [[gnu::cleanup(cleanup_free)]] =
        strdup(path_suffix);
    if (path_components == nullptr) {
        rc = errno;
        goto Done;
    }
    for (dir_name = strtok_r(path_components, "/", &tokctx); dir_name;
         dir_name = strtok_r(nullptr, "/", &tokctx)) {
        // This loop iterates over the path components in a path string; each
        // path component is expected to be the name of a directory.
        //
        // Within this loop, `dir_name` refers to the next path component and
        // `curfd` is an open file descriptor to the parent directory of
        // `dir_name`; the "walk" involves:
        //
        //   - appending the `dir_name` to `pathbuf`; we do this first so that
        //     the user can tell which path segment an errno(3) code applies to
        //     in case one of the next steps fails
        //
        //   - creating a directory named `dir_name` if it doesn't exist and
        //     we're allowed to create directories
        //
        //   - opening a file descriptor to `dir_name` as the new `curfd` with
        //     O_DIRECTORY (thereby checking if it is a directory in case we
        //     got EEXIST from mkdirat(2) but it is some other type of file)
        //
        // When we're done, `curfd` is an open file descriptor to the last
        // directory in the path
        int nextfd;
        int prevfd;
        if (pathbuf != nullptr) {
            rc = monad_path_append(&pathbuf, dir_name, &pathbuf_size);
            if (rc != 0) {
                goto Done;
            }
        }
        if (can_create_dirs && mkdirat(curfd, dir_name, mode) == -1 &&
            errno != EEXIST) {
            rc = errno;
            goto Done;
        }
        nextfd = openat(curfd, dir_name, OPEN_FLAGS);
        if (nextfd == -1) {
            rc = errno;
            goto Done;
        }
        prevfd = curfd;
        curfd = nextfd;
        tidy_close(prevfd);
    }

Done:
    if (final_dirfd != nullptr && rc == 0) {
        *final_dirfd = curfd;
    }
    else {
        tidy_close(curfd);
    }
    return rc;
    // NOLINTEND(clang-analyzer-unix.Malloc)
}
