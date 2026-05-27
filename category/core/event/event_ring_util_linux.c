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
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <fcntl.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <sys/types.h>

#include <category/core/cleanup.h> // NOLINT(misc-include-cleaner)
#include <category/core/event/event_ring_util.h>
#include <category/core/format_err.h>
#include <category/core/srcloc.h>

// Defined in event_ring.c, so we can share monad_event_ring_get_last_error()
extern thread_local char _g_monad_event_ring_error_buf[1024];

#define FORMAT_ERRC(...)                                                       \
    monad_format_err(                                                          \
        _g_monad_event_ring_error_buf,                                         \
        sizeof(_g_monad_event_ring_error_buf),                                 \
        &MONAD_SOURCE_LOCATION_CURRENT(),                                      \
        __VA_ARGS__)

static bool check_flock_entry(
    char *const lock_line, ino_t const ring_ino,
    struct monad_event_flock_info *const fl_info)
{
    char *saveptr;
    ino_t lock_ino = 0;
    unsigned tok_num = 0;

    for (char const *tok = strtok_r(lock_line, " ", &saveptr);
         tok != nullptr && tok_num <= 5;
         tok = strtok_r(nullptr, " ", &saveptr), ++tok_num) {
        switch (tok_num) {
        case 1:
            if (strcmp(tok, "FLOCK") != 0) {
                return false;
            }
            break;

        case 2:
            if (strcmp(tok, "ADVISORY") != 0) {
                return false;
            }
            break;

        case 3:
            if (strcmp(tok, "WRITE") == 0) {
                fl_info->lock = LOCK_EX;
            }
            else if (strcmp(tok, "READ") == 0) {
                fl_info->lock = LOCK_SH;
            }
            else {
                return false;
            }
            break;

        case 4:
            if (sscanf(tok, "%d", &fl_info->pid) != 1) {
                return false;
            }
            break;

        case 5:
            if (sscanf(tok, "%*x:%*x:%ju", &lock_ino) != 1) {
                return false;
            }
            break;

        default:
            break;
        }
    }

    return lock_ino == ring_ino;
}

int monad_event_ring_query_flocks(
    int const ring_fd, struct monad_event_flock_info *const flocks,
    size_t *const size)
{
    struct stat ring_stat;
    struct monad_event_flock_info fl_info_buf;
    size_t const capacity = *size;
    char info_buf[128];
    FILE *lock_info_file [[gnu::cleanup(cleanup_fclose)]] = nullptr;

    *size = 0;
    if (fstat(ring_fd, &ring_stat) == -1) {
        return FORMAT_ERRC(errno, "fstat failed");
    }
    lock_info_file = fopen("/proc/locks", "r");
    if (lock_info_file == nullptr) {
        return FORMAT_ERRC(errno, "fopen of /proc/locks failed");
    }
    while (fgets(info_buf, sizeof info_buf, lock_info_file) != nullptr) {
        if (check_flock_entry(info_buf, ring_stat.st_ino, &fl_info_buf)) {
            if (*size == capacity) {
                return FORMAT_ERRC(ERANGE, "more flocks than copy-out space");
            }
            flocks[(*size)++] = fl_info_buf;
        }
    }
    return 0; // NOLINT(clang-analyzer-unix.Stream)
}
