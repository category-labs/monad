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

#include <dirent.h>
#include <fcntl.h>
#include <linux/magic.h>
#include <stdint.h>
#include <sys/stat.h>
#include <sys/statfs.h>
#include <sys/types.h>
#include <sys/vfs.h>
#include <unistd.h>

#include <category/core/event/event_ring.h>
#include <category/core/event/event_ring_util.h>
#include <category/core/format_err.h>
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

// Given a path which may not exist, walk backward until we find a parent path
// that does exist; the caller must free(3) parent_path
static int find_existing_parent_path(char const *path, char **parent_path)
{
    struct stat path_stat;

    *parent_path = nullptr;
    if (strlen(path) == 0) {
        return FORMAT_ERRC(EINVAL, "path cannot be nullptr or empty");
    }
    *parent_path = strdup(path);

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

/*
 * The next three functions perform the following task:
 *
 * Given an inode number for a file, find the pids of all processes that have
 * opened this file with open(2) mode O_WRONLY or O_RDWR. The responsibility
 * is divided as follows:
 *
 * is_writer_fd - knows how to parse the format a single /proc/<pid>/fdinfo/<fd>
 *     entry, extracting the descriptor's inode number and open(2) flags
 *
 * scan_file_table_for_writer - given a pid for a single candidate process and
 *     the inode number of a file, walk the /proc/<pid>/fdinfo directory entries
 *     (the open file table) and call is_writer_fd on each one
 *
 * find_writer_pids_by_ino - given an inode number of a file, scan the file
 *     table of all processes we have access to by iterating through the /proc
 *     directory and calling scan_file_table_for_writer for each process
 */

static bool is_writer_fd(ino_t ring_ino, int fdinfo_entry)
{
    // The format of an fdinfo file (as of Linux 6.16, see proc/fd.c) is:
    //
    //   "pos:\t%lli\nflags:\t0%o\nmnt_id:\t%i\nino:\t%lu\n"
    //
    // This will definitely fit in READ_BUF_SIZE bytes, if not the format
    // must have changed somehow and we won't try to parse it.
    constexpr char FDINFO_DELIM[] = "\t :";
    constexpr size_t READ_BUF_SIZE = 256;
    char read_buf[READ_BUF_SIZE];
    char *scan = read_buf;
    char *line;

    ssize_t const n_read = read(fdinfo_entry, read_buf, sizeof read_buf);
    if (n_read == -1 || n_read == READ_BUF_SIZE) {
        return false;
    }
    bool is_write = false;
    bool is_ino = false;

    read_buf[n_read] = '\0'; // In case of a short read
    while ((line = strsep(&scan, "\n"))) {
        char *key = nullptr;
        char *value = nullptr;
        key = strsep(&line, FDINFO_DELIM);
        while (line != nullptr) {
            value = strsep(&line, FDINFO_DELIM);
        }

        if (key != nullptr && strcmp(key, "flags") == 0 && value != nullptr) {
            unsigned long const flags = strtoul(value, nullptr, 0);
            is_write = flags & O_WRONLY || flags & O_RDWR;
        }
        if (key != nullptr && strcmp(key, "ino") == 0 && value != nullptr) {
            unsigned long const ino = strtoul(value, nullptr, 10);
            is_ino = ino == ring_ino;
        }
    }

    return is_write && is_ino;
}

static int
scan_file_table_for_writer(ino_t ring_ino, pid_t pid, bool *writer_found)
{
    char fdinfo_dir_name[32];
    struct dirent *fdinfo_dir_ent;
    int rc = 0;
    *writer_found = false;

    snprintf(fdinfo_dir_name, sizeof fdinfo_dir_name, "/proc/%d/fdinfo", pid);
    DIR *fdinfo_dir = opendir(fdinfo_dir_name);
    if (fdinfo_dir == nullptr) {
        return FORMAT_ERRC(errno, "opendir failed for %s", fdinfo_dir_name);
    }
    int const fdinfo_dir_fd = dirfd(fdinfo_dir);
    if (fdinfo_dir_fd == -1) {
        rc = FORMAT_ERRC(errno, "dirfd failed");
        goto Done;
    }
    errno = 0;
    while ((fdinfo_dir_ent = readdir(fdinfo_dir)) != nullptr &&
           *writer_found == false) {
        int entry = openat(fdinfo_dir_fd, fdinfo_dir_ent->d_name, O_RDONLY);
        if (entry != -1) {
            *writer_found = is_writer_fd(ring_ino, entry);
        }
        (void)close(entry);
        errno = 0;
    }
    if (errno != 0) {
        rc = FORMAT_ERRC(errno, "readdir(3) failed");
    }
Done:
    (void)closedir(fdinfo_dir);
    return rc;
}

static int find_writer_pids_by_ino(
    ino_t const ring_ino, pid_t *pids, size_t const pid_in_size,
    size_t *pid_out_size)
{
    struct dirent *proc_dir_ent;
    DIR *proc_dir;
    int rc = 0;

    *pid_out_size = 0;
    proc_dir = opendir("/proc");
    if (proc_dir == nullptr) {
        return FORMAT_ERRC(errno, "opendir(\"/proc\") failed");
    }
    errno = 0;
    while ((proc_dir_ent = readdir(proc_dir)) != nullptr &&
           *pid_out_size < pid_in_size) {
        char *end_ptr;
        pid_t const pid = (pid_t)strtol(proc_dir_ent->d_name, &end_ptr, 10);
        if (*end_ptr != '\0') {
            // The file name does not consistent entirely of numbers; this is
            // not a process entry
            continue;
        }
        bool writer_found;
        (void)scan_file_table_for_writer(ring_ino, pid, &writer_found);
        if (writer_found) {
            pids[(*pid_out_size)++] = pid;
        }
        errno = 0;
    }
    if (errno != 0) {
        rc = FORMAT_ERRC(errno, "readdir(3) failed");
    }
    (void)closedir(proc_dir);
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
    if (fallocate(ring_fd, 0, ring_offset, (off_t)ring_bytes) == -1) {
        return FORMAT_ERRC(
            errno,
            "fallocate failed for event ring file `%s`, size %lu",
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

int monad_event_ring_find_writer_pids(
    int ring_fd, pid_t *pids, size_t *pids_size)
{
    struct stat ring_stat;
    if (pids == nullptr) {
        return FORMAT_ERRC(EFAULT, "pids cannot be nullptr");
    }
    if (pids_size == nullptr) {
        return FORMAT_ERRC(EFAULT, "pids_size cannot be nullptr");
    }
    if (fstat(ring_fd, &ring_stat) == -1) {
        return FORMAT_ERRC(errno, "fstat of ring_fd %d failed", ring_fd);
    }
    return find_writer_pids_by_ino(
        ring_stat.st_ino, pids, *pids_size, pids_size);
}

int monad_check_path_supports_map_hugetlb(char const *path, bool *supported)
{
    char *parent_path;
    struct statfs fs_stat;
    int rc;

    *supported = false;
    rc = find_existing_parent_path(path, &parent_path);
    if (rc != 0 || parent_path == nullptr) {
        goto Done;
    }
    if (statfs(parent_path, &fs_stat) == -1) {
        rc = FORMAT_ERRC(errno, "statfs of `%s` failed", parent_path);
        goto Done;
    }
    else {
        // Only hugetlbfs supports MAP_HUGETLB
        *supported = fs_stat.f_type == HUGETLBFS_MAGIC;
        rc = 0;
    }
Done:
    free(parent_path);
    return rc;
}

// libhugetlbfs is always present for Category Labs, but when this is compiled
// by third parties using the SDK, it is optional
#if MONAD_EVENT_DISABLE_LIBHUGETLBFS

int monad_event_open_ring_dir_fd(int *, char *, size_t)
{
    return FORMAT_ERRC(ENOSYS, "compiled without libhugetlbfs support");
}

#else

int monad_event_open_ring_dir_fd(int *dirfd, char *namebuf, size_t namebuf_size)
{
    // Create MONAD_EVENT_DEFAULT_RING_DIR with rwxrwxr-x
    constexpr mode_t mode = S_IRWXU | S_IRWXG | S_IROTH | S_IXOTH;
    struct monad_hugetlbfs_resolve_params const params = {
        .page_size = 1UL << 21,
        .path_suffix = MONAD_EVENT_DEFAULT_RING_DIR,
        .create_dirs = true,
        .dir_create_mode = mode};
    int const rc =
        monad_hugetlbfs_open_dir_fd(&params, dirfd, namebuf, namebuf_size);
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
