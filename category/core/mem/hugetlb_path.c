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

#include <ctype.h>
#include <errno.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <fcntl.h>
#include <linux/limits.h>
#include <linux/magic.h>
#include <mntent.h>
#include <sys/stat.h>
#include <sys/vfs.h>
#include <unistd.h>

thread_local char g_error_buf[PATH_MAX];

#define FORMAT_ERRC(...)                                                       \
    monad_format_err(                                                          \
        g_error_buf,                                                           \
        sizeof g_error_buf,                                                    \
        &MONAD_SOURCE_LOCATION_CURRENT(),                                      \
        __VA_ARGS__)

// Simple function for parsing human-readable sizes like "256 kB", "8M" or "1G"
static int expand_byte_size(char const *const text, size_t *const size)
{
    char code;

    // Match <number> <any number of spaces> <unit>
    // <unit> can be absent or equal to 'k', 'M', 'G'
    switch (sscanf(text, "%zu %c", size, &code)) {
    case 1:
        return 0;
    case 2:
        break;
    default:
        return FORMAT_ERRC(EBADMSG, "number does not have expected format");
    }
    switch (tolower((unsigned char)code)) {
    case 'k':
        *size <<= 10;
        break;
    case 'm':
        *size <<= 20;
        break;
    case 'g':
        *size <<= 30;
        break;
    default:
        return FORMAT_ERRC(EBADMSG, "unrecognized size code %c", code);
    }
    return 0;
}

// NOLINTBEGIN(clang-analyzer-unix.Stream)

static int find_hugetlbfs_path_for_size(
    size_t const required_pagesize, char *const pathbuf,
    size_t const pathbuf_size, size_t *const mount_path_len)
{
    // Linux limits the mount options string to the size of one page and
    // PATH_MAX is also one page; strbuf has to hold both of these, plus extra
    constexpr size_t BUFFER_SIZE = 4096 * 3;
    char strbuf[BUFFER_SIZE];
    struct mntent mount;
    constexpr char MOUNTS_PATH[] = "/proc/mounts";
    FILE *mounts_file [[gnu::cleanup(cleanup_fclose)]] = nullptr;

    *mount_path_len = 0;
    mounts_file = fopen(MOUNTS_PATH, "r");
    if (mounts_file == nullptr) {
        return FORMAT_ERRC(errno, "fopen of %s failed", MOUNTS_PATH);
    }

    // Walk the mount table described by `mounts_file` (has fstab(5) format)
    while (getmntent_r(mounts_file, &mount, strbuf, sizeof strbuf)) {
        struct statfs mnt_stat;

        if (statfs(mount.mnt_dir, &mnt_stat) != 0 ||
            mnt_stat.f_type != HUGETLBFS_MAGIC ||
            (size_t)mnt_stat.f_bsize != required_pagesize) {
            // Couldn't stat, or not hugetlbfs, or wrong pagesize; keep looking
            continue;
        }

        // We found a hugetlbfs mount with the required hugepage size, check
        // if we can access it; if so, return success
        if (access(mount.mnt_dir, R_OK | W_OK | X_OK) == 0) {
            *mount_path_len = strlcpy(pathbuf, mount.mnt_dir, pathbuf_size);
            if (*mount_path_len >= pathbuf_size) {
                return FORMAT_ERRC(
                    ERANGE, "pathbuf too small to hold %s", mount.mnt_dir);
            }
            return 0;
        }
    }

    if (ferror(mounts_file)) {
        // getmntent_r(3) returned nullptr because of a file read error
        return FORMAT_ERRC(
            errno, "getmntent_r(3) error while reading %s", MOUNTS_PATH);
    }

    // getmntent_r(3) returned nullptr because we visited all mounts; no
    // accessible hugetlbfs mount was found
    return FORMAT_ERRC(
        ENODEV,
        "no mounted hugetlbfs with pagesize %zu is accessible to this user",
        required_pagesize);
}

// NOLINTEND(clang-analyzer-unix.Stream)

// Given a path which may not exist, walk backward until we find a parent path
// that does exist; the caller must free(3) parent_path
static int
find_existing_parent_path(char const *const path, char **const parent_path)
{
    struct stat path_stat;

    *parent_path = nullptr;
    if (strlen(path) == 0) {
        return FORMAT_ERRC(EINVAL, "path cannot be nullptr or empty");
    }
    *parent_path = strdup(path); // Freed by the caller
    if (*parent_path == nullptr) {
        return FORMAT_ERRC(errno, "strdup of %s failed", path);
    }

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

int monad_hugetlbfs_open_dir_fd(
    struct monad_hugetlbfs_resolve_params const *const params, int *const dirfd,
    char *pathbuf, size_t pathbuf_size)
{
    int rc;
    size_t resolve_size;
    size_t mount_path_len;
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
        rc = monad_get_default_hugepage_size(&resolve_size);
        if (rc != 0) {
            return rc;
        }
    }
    else {
        resolve_size = params->page_size;
    }
    rc = find_hugetlbfs_path_for_size(
        resolve_size, pathbuf, pathbuf_size, &mount_path_len);
    if (rc != 0) {
        return rc;
    }
    int mountfd [[gnu::cleanup(cleanup_close)]] = open(pathbuf, OPEN_FLAGS);
    if (mountfd == -1) {
        return FORMAT_ERRC(
            errno, "open of hugetlbfs mount `%s` failed", pathbuf);
    }
    rc = monad_path_open_subdir(
        mountfd,
        params->path_suffix,
        params->create_dirs ? params->dir_create_mode : MONAD_PATH_NO_CREATE,
        dirfd,
        pathbuf + mount_path_len,
        pathbuf_size - mount_path_len);
    if (rc != 0) {
        return FORMAT_ERRC(
            rc,
            "monad_path_open_subdir of `%s` underneath `%.*s` failed at last "
            "path component of `%s`",
            params->path_suffix,
            (int)mount_path_len,
            pathbuf,
            pathbuf);
    }
    return 0;
}

// NOLINTBEGIN(clang-analyzer-unix.Stream)

int monad_get_default_hugepage_size(size_t *const pagesize)
{
    char info_buf[256];
    constexpr char MEMINFO_PATH[] = "/proc/meminfo";
    constexpr char HUGEPAGE_SIZE[] = "Hugepagesize:";
    FILE *meminfo_file [[gnu::cleanup(cleanup_fclose)]] = nullptr;

    if (pagesize == nullptr) {
        return FORMAT_ERRC(EFAULT, "pagesize must not be null");
    }
    meminfo_file = fopen(MEMINFO_PATH, "r");
    if (meminfo_file == nullptr) {
        return FORMAT_ERRC(errno, "fopen of %s failed", MEMINFO_PATH);
    }
    while (fgets(info_buf, sizeof info_buf, meminfo_file) != nullptr) {
        char const *p;

        if (strncmp(info_buf, HUGEPAGE_SIZE, sizeof(HUGEPAGE_SIZE) - 1) != 0) {
            continue;
        }
        p = info_buf + sizeof HUGEPAGE_SIZE - 1;
        while (isspace((unsigned char)*p)) {
            ++p;
        }
        return expand_byte_size(p, pagesize);
    }
    return FORMAT_ERRC(EOPNOTSUPP, "no system default hugepage size");
}

// NOLINTEND(clang-analyzer-unix.Stream)

int monad_hugetlbfs_check_path(char const *const path, bool *const is_hugetlbfs)
{
    char *parent_path;
    struct statfs fs_stat;
    int rc;

    if (path == nullptr || is_hugetlbfs == nullptr) {
        return FORMAT_ERRC(EFAULT, "nullptr not allowed here");
    }
    *is_hugetlbfs = false;
    rc = find_existing_parent_path(path, &parent_path);
    if (rc != 0) {
        goto Done;
    }
#if defined(__clang__)
    // True when rc == 0, but clang-tidy cannot figure this out
    __builtin_assume(parent_path != nullptr);
#endif
    if (statfs(parent_path, &fs_stat) == -1) {
        rc = FORMAT_ERRC(errno, "statfs of `%s` failed", parent_path);
        goto Done;
    }
    else {
        *is_hugetlbfs = fs_stat.f_type == HUGETLBFS_MAGIC;
        rc = 0;
    }
Done:
    free(parent_path);
    return rc;
}

char const *monad_hugetlbfs_get_last_error()
{
    return g_error_buf;
}
