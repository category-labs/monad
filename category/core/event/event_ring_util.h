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
 * Defines convenience functions that are useful in most event ring programs,
 * but which are not part of the core API
 */

#include <stddef.h>
#include <stdint.h>

#include <sys/types.h>

#ifdef __cplusplus
extern "C"
{
#endif

enum monad_event_content_type : uint16_t;
struct monad_event_ring;

/// Value passed to monad_event_resolve_ring_file's `default_path` parameter,
/// to request the hugetlbfs path that is dynamically computed by libhugetlbfs
constexpr char const *MONAD_EVENT_DEFAULT_HUGETLBFS = nullptr;

/// Arguments for the `monad_event_ring_init_simple` function
struct monad_event_ring_simple_config
{
    uint8_t descriptors_shift;
    uint8_t payload_buf_shift;
    uint16_t context_large_pages;
    enum monad_event_content_type content_type;
    uint8_t const *schema_hash;
};

/// Output structure returned by `monad_event_ring_query_flocks`
struct monad_event_flock_info
{
    int lock; ///< Type of lock held (LOCK_EX or LOCK_SH)
    pid_t pid; ///< Process holding lock
};

/// "All in one" convenience event ring file init for simple cases: given an
/// event ring fd and the required options, calculate the required size of the
/// event ring, call fallocate(2) to ensure the storage is available, then call
/// monad_event_ring_init_file
int monad_event_ring_init_simple(
    struct monad_event_ring_simple_config const *, int ring_fd,
    off_t ring_offset, char const *error_name);

/// Check that the event ring content type and schema hash match the assumed
/// values
int monad_event_ring_check_content_type(
    struct monad_event_ring const *, enum monad_event_content_type,
    uint8_t const *schema_hash);

/// Query information about every process that holds an flock on the file
/// referred to by the given file descriptor; the flock(2) system call is used
/// to detect which processes are writing to an event ring file: exclusive
/// writers place a LOCK_EX lock, shared writers all place LOCK_SH locks
int monad_event_ring_query_flocks(
    int ring_fd, struct monad_event_flock_info *, size_t *size);

/// For event ring files that have an exclusive writer, determine the pid of
/// that writer; this is a convenience wrapper around the
/// monad_event_ring_query_flocks function
int monad_event_ring_query_excl_writer_pid(int ring_fd, pid_t *pid);

/// Given a path to a file (which does not need to exist), check if the
/// associated file system supports that file being mmap'ed with MAP_HUGETLB
int monad_check_path_supports_map_hugetlb(char const *path, bool *supported);

/// Open a directory fd, for use in openat(2), to the default subdirectory on
/// a hugetlbfs filesystem that is used to hold event ring files; also computes
/// the full path to this directory; this is a wrapper around the generic API
/// function `monad_hugetlbfs_open_dir_fd`
int monad_event_open_hugetlbfs_dir_fd(
    int *dirfd, char *pathbuf, size_t pathbuf_size);

/// Given an event ring file input (typically from the command line), resolve it
/// to a file relative to the directory `default_path` if it does not contain
/// any '/' characters, i.e., if it is a "pure" filename; if it contains a '/'
/// character then copy it as-is, so that it will resolve relative to getcwd(2),
/// similar to how a UNIX shell resolves command names; if `default_path` is
/// MONAD_EVENT_DEFAULT_HUGETLBFS, this calls monad_event_open_hugetlbfs_dir_fd
int monad_event_resolve_ring_file(
    char const *default_path, char const *file, char *pathbuf,
    size_t pathbuf_size);

constexpr char MONAD_EVENT_DEFAULT_RING_DIR[] = "event-rings";

#ifdef __cplusplus
} // extern "C"
#endif
