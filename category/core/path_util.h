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
 * This file contains helper functions for working with path strings in C
 * APIs
 */

#include <stddef.h>
#include <sys/types.h>

#ifdef __cplusplus
extern "C"
{
#endif

/// Value to pass for the `mode` parameter in monad_path_open_subdir if it
/// is not allowed to create subdirectories
constexpr mode_t MONAD_PATH_NO_CREATE = (mode_t)0;

// Appends a '/' followed by the contents of src to dst; this behaves like
// stpecpy (always null-terminated and designed for chain-copying, so dst and
// size are adjusted); if truncated, ENAMETOOLONG is returned; dst must be set
// up to append when called, i.e., EINVAL is returned unless **dst == '\0'
int monad_path_append(char **dst, char const *src, size_t *size);

// A helper function which starts at the open directory file descriptor
// `init_dirfd` and opens subdirectory paths along `path_suffix`, creating any
// non-existent subdirs if `mode & ACCESSPERMS` is not zero; each path segment
// is appended to `pathbuf` as it is translated, so that the last appended path
// component is the one associated with the error if one occurs; on success,
// final_dirfd will hold an open descriptor to the final subdirectory
int monad_path_open_subdir(
    int init_dirfd, char const *path_suffix, mode_t mode, int *final_dirfd,
    char *pathbuf, size_t pathbuf_size);

#ifdef __cplusplus
} // extern "C"
#endif
