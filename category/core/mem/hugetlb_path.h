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

#pragma once

/**
 * @file
 *
 * Helper utility for resolving hugetlbfs paths
 */

#include <stddef.h>
#include <sys/types.h>

#ifdef __cplusplus
extern "C"
{
#endif

// clang-format off

/// Arguments to monad_hugetlbfs_open_dir_fd
struct monad_hugetlbfs_resolve_params
{
    size_t page_size;        ///< Required size of huge pages, 0 for default
    char const *path_suffix; ///< Dir names to append after hugepage mountpoint
    bool create_dirs;        ///< True -> create suffix dirs if not existing
    mode_t dir_create_mode;  ///< mode param for mkdir(2), if create_dirs
};

// clang-format on

/// Open a directory fd, for use in openat(2), to some subdirectory on a
/// hugetlbfs filesystem; the mount point of the filesystem will be used if
/// path_suffix is nullptr. If desired, the subdirectory will be created if it
/// does not exist. This also formats the full name of the absolute path to
/// the subdirectory into pathbuf, if it is not nullptr.
int monad_hugetlbfs_open_dir_fd(
    struct monad_hugetlbfs_resolve_params const *, int *dirfd, char *pathbuf,
    size_t pathbuf_size);

/// Return the last error that occurred on this thread
char const *monad_hugetlbfs_get_last_error();

#ifdef __cplusplus
} // extern "C"
#endif
