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
#include <stdlib.h>
#include <string.h>

#include <dirent.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#include <category/core/cleanup.h>
#include <category/core/event/evcap_file.h>
#include <category/core/event/evcap_reader.h>
#include <category/core/event/evcap_writer.h>
#include <category/core/event/event_def.h>
#include <category/core/event/event_ring.h>
#include <category/core/format_err.h>
#include <category/core/path_util.h>
#include <category/core/srcloc.h>
#include <category/execution/ethereum/event/blockcap.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

// Defined in blockcap_builder.c
extern thread_local char _g_monad_bcap_error_buf[1024];

#define FORMAT_ERRC(...)                                                       \
    monad_format_err(                                                          \
        _g_monad_bcap_error_buf,                                               \
        sizeof(_g_monad_bcap_error_buf),                                       \
        &MONAD_SOURCE_LOCATION_CURRENT(),                                      \
        __VA_ARGS__)

struct monad_bcap_archive
{
    int dirfd;
};

static int compare_uint64_t(void const *lhs, void const *rhs)
{
    return *(uint64_t const *)lhs < *(uint64_t const *)rhs    ? -1
           : *(uint64_t const *)lhs == *(uint64_t const *)rhs ? 0
                                                              : 1;
}

static inline uint64_t block_to_subdir(uint64_t b)
{
    return (b / MONAD_BCAP_ARCHIVE_FILES_PER_SUBDIR) *
           MONAD_BCAP_ARCHIVE_FILES_PER_SUBDIR;
}

struct scan_dir_result
{
    uint64_t *values;
    size_t len;
    uint64_t min;
    uint64_t max;
};

enum archive_scan_type
{
    ST_GROUP_SUBDIRS,
    ST_BLOCK_FILES,
};

static int scan_archive_dir(
    struct monad_bcap_archive const *bca, enum archive_scan_type type,
    uint64_t subdir, struct scan_dir_result *r)
{
    struct dirent *de;
    int rc;
    DIR *dir;
    int dirfd;
    uint64_t last_value = 0;
    bool is_sorted = true;
    size_t capacity = type == ST_GROUP_SUBDIRS ? 256 : 10'000;

    memset(r, 0, sizeof *r);
    if (type == ST_GROUP_SUBDIRS) {
        dirfd = dup(bca->dirfd);
        if (dirfd == -1) {
            return FORMAT_ERRC(errno, "dup of block archive dirfd failed");
        }
    }
    else {
        char subdir_buf[32];
        sprintf(subdir_buf, "%lu", (unsigned long)subdir);
        dirfd =
            openat(bca->dirfd, subdir_buf, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
        if (dirfd == -1) {
            return FORMAT_ERRC(errno, "openat of subdir %s failed", subdir_buf);
        }
    }
    dir = fdopendir(dirfd);
    if (dir == nullptr) {
        (void)close(dirfd);
        return FORMAT_ERRC(errno, "fdopendir failed");
    }
    rewinddir(dir);

    r->values = realloc(nullptr, sizeof(uint64_t) * capacity);
    if (r->values == nullptr) {
        rc = FORMAT_ERRC(errno, "realloc of size %zu failed", capacity);
        closedir(dir);
        return rc;
    }

    errno = 0;
    unsigned long dir_entries = 0;
    unsigned long valid_entries = 0;
    while ((de = readdir(dir)) != nullptr) {
        char *end;
        unsigned long value;

        ++dir_entries;
        if (type == ST_GROUP_SUBDIRS) {
            if (de->d_type != DT_DIR) {
                continue;
            }
            if (de->d_name[0] == '.') {
                // Don't count any '.'-prefixed directory as invalid
                ++valid_entries;
                continue;
            }
            value = strtoul(de->d_name, &end, 10);
            if (*end != '\0' || value == 0) {
                continue;
            }
        }
        else {
            if (sscanf(de->d_name, "%lu.bcap", &value) != 1) {
                continue;
            }
        }
        ++valid_entries;
        if (r->len == capacity) {
            capacity *= 2;
            uint64_t *const new_address =
                realloc(r->values, sizeof(uint64_t) * capacity);
            if (new_address == nullptr) {
                rc = FORMAT_ERRC(errno, "realloc of size %zu failed", capacity);
                free(r->values);
                closedir(dir);
                return rc;
            }
            r->values = new_address;
        }
        r->values[r->len++] = value;
        is_sorted &= last_value == 0 || value == last_value + 1;
        last_value = value;
        errno = 0;
    }
    if (dir_entries > valid_entries && valid_entries == 2) {
        return FORMAT_ERRC(
            EINVAL, "directory does not appear to be a blockcap archive");
    }
    if (errno != 0) {
        closedir(dir);
        return FORMAT_ERRC(errno, "readdir(3) error for type %d", type);
    }
    if (!is_sorted) {
        qsort(r->values, r->len, sizeof(uint64_t), compare_uint64_t);
    }
    if (r->len > 0) {
        r->min = r->values[0];
        r->max = r->values[r->len - 1];
    }
    closedir(dir);
    return 0;
}

static int append_missing_block(
    uint64_t missing_block, struct monad_bcap_block_range_list *missing_ranges,
    struct monad_bcap_block_range **last_range_p)
{
    struct monad_bcap_block_range *new_range;
    struct monad_bcap_block_range *last_range;

    last_range = TAILQ_LAST(&missing_ranges->head, monad_bcap_block_range_head);
    if (last_range != nullptr && last_range->max + 1 == missing_block) {
        last_range->max = missing_block;
    }
    else {
        new_range = malloc(sizeof *new_range);
        if (new_range == nullptr) {
            return FORMAT_ERRC(errno, "malloc failed");
        }
        new_range->min = missing_block;
        new_range->max = missing_block;
        TAILQ_INSERT_TAIL(&missing_ranges->head, new_range, next);
        last_range = new_range;
    }
    if (last_range_p != nullptr) {
        *last_range_p = last_range;
    }

    return 0;
}

int monad_bcap_archive_open(
    struct monad_bcap_archive **bca_p, int dirfd, char const *error_name)
{
    int rc;
    struct stat archive_stat;

    struct monad_bcap_archive *bca = *bca_p = malloc(sizeof *bca);
    if (bca == nullptr) {
        return FORMAT_ERRC(errno, "malloc of monad_bcap_archive failed");
    }
    bca->dirfd = dup(dirfd);
    if (bca->dirfd == -1) {
        rc =
            FORMAT_ERRC(errno, "dup of fd for archive `%s` failed", error_name);
        goto Error;
    }
    if (fstat(bca->dirfd, &archive_stat) == -1) {
        rc = FORMAT_ERRC(errno, "stat of archive `%s` file failed", error_name);
        goto Error;
    }
    if ((archive_stat.st_mode & S_IFDIR) != S_IFDIR) {
        rc = FORMAT_ERRC(ENOTDIR, "path `%s` is not directory", error_name);
        goto Error;
    }
    return 0;

Error:
    monad_bcap_archive_close(bca);
    *bca_p = nullptr;
    return rc;
}

void monad_bcap_archive_close(struct monad_bcap_archive *bca)
{
    if (bca != nullptr) {
        (void)close(bca->dirfd);
        free(bca);
    }
}

int monad_bcap_archive_get_dirfd(struct monad_bcap_archive const *bca)
{
    return bca->dirfd;
}

int monad_bcap_archive_format_block_path(
    uint64_t block_number, char *path_buf, size_t path_buf_size,
    char const **subdir_end)
{
    int rc;
    char file_name_buf[32];

    rc = snprintf(
        path_buf,
        path_buf_size,
        "%lu",
        (unsigned long)block_to_subdir(block_number));
    if (rc < 0) {
        return FORMAT_ERRC(EINVAL, "snprintf error: %d", rc);
    }
    if ((size_t)rc >= path_buf_size) {
        return FORMAT_ERRC(
            ENAMETOOLONG,
            "path buffer size %zu is not large enough",
            path_buf_size);
    }
    // Advance path_buf so we can use monad_path_append with it, and remember
    // when the subdirectory ends
    path_buf += rc;
    path_buf_size -= (size_t)rc;
    if (subdir_end != nullptr) {
        *subdir_end = path_buf;
    }
    (void)sprintf(file_name_buf, "%lu.bcap", (unsigned long)block_number);
    rc = monad_path_append(&path_buf, file_name_buf, &path_buf_size);
    if (rc != 0) {
        return FORMAT_ERRC(
            rc, "path append of %s to %s failed", file_name_buf, path_buf);
    }
    return 0;
}

int monad_bcap_archive_open_block_reader(
    struct monad_bcap_archive const *bca, uint64_t block_number, char *path_buf,
    size_t path_buf_size, int *fd_out,
    struct monad_evcap_reader **evcap_reader_p,
    struct monad_evcap_section_desc const **event_bundle_sd_p)
{
    int rc;
    int fd;
    char local_path_buf[64];
    struct monad_evcap_section_desc const *scan_sd;
    struct monad_evcap_section_desc const *event_sd;

    *evcap_reader_p = nullptr;
    if (event_bundle_sd_p != nullptr) {
        *event_bundle_sd_p = nullptr;
    }
    if (path_buf == nullptr) {
        path_buf = local_path_buf;
        path_buf_size = sizeof local_path_buf;
    }
    rc = monad_bcap_archive_open_block_fd(
        bca, block_number, O_RDONLY, 0, 0, path_buf, path_buf_size, &fd);
    if (rc != 0) {
        return rc;
    }

    // Create an event capture reader for the file, and check if the schema
    // is compatible with the current library
    rc = monad_evcap_reader_create(evcap_reader_p, fd, path_buf);
    if (fd_out != nullptr) {
        *fd_out = fd;
    }
    else {
        (void)close(fd);
    }
    if (rc != 0) {
        return FORMAT_ERRC(
            rc,
            "could not open evcap reader for %s; caused by:\n%s",
            path_buf,
            monad_evcap_reader_get_last_error());
    }
    if (monad_evcap_reader_check_schema(
            *evcap_reader_p,
            MONAD_EVENT_RING_HEADER_VERSION,
            MONAD_EVENT_CONTENT_TYPE_EXEC,
            g_monad_exec_event_schema_hash) != 0) {
        return FORMAT_ERRC(
            rc,
            "evcap reader schema check failed for %s; caused by:\n%s",
            path_buf,
            monad_evcap_reader_get_last_error());
    }

    // Find an EVENT_BUNDLE section with the EXEC content type and an explicitly
    // set block number; if there's more than one, it's an error
    scan_sd = nullptr;
    event_sd = nullptr;
    while (monad_evcap_reader_next_section(
        *evcap_reader_p, MONAD_EVCAP_SECTION_EVENT_BUNDLE, &scan_sd)) {
        struct monad_evcap_section_desc const *const schema_sd =
            monad_evcap_reader_load_linked_section_desc(
                *evcap_reader_p, scan_sd->event_bundle.schema_desc_offset);
        if (schema_sd->schema.content_type != MONAD_EVENT_CONTENT_TYPE_EXEC) {
            continue;
        }
        if (scan_sd->event_bundle.block_number == 0) {
            continue;
        }
        if (event_sd != nullptr) {
            return FORMAT_ERRC(
                EOVERFLOW,
                "duplicate block event bundle sections in %s",
                path_buf);
        }
        event_sd = scan_sd;
    }

    if (event_bundle_sd_p != nullptr) {
        *event_bundle_sd_p = event_sd;
    }

    return 0;
}

int monad_bcap_archive_open_block_writer(
    struct monad_bcap_archive *bca, uint64_t block_number,
    mode_t dir_create_mode, mode_t file_create_mode, char *path_buf,
    size_t path_buf_size, int *fd_out,
    struct monad_evcap_writer **evcap_writer_p,
    struct monad_evcap_section_desc const **schema_sd_p)
{
    int rc;
    int block_fd;
    char local_path_buf[64];
    struct monad_evcap_section_desc const *schema_sd;
    struct monad_evcap_writer_create_options const evcap_writer_opts = {
        .sectab_entries_shift = 0, .append = false};

    *evcap_writer_p = nullptr;
    if (path_buf == nullptr) {
        path_buf = local_path_buf;
        path_buf_size = sizeof local_path_buf;
    }
    if (fd_out != nullptr) {
        *fd_out = -1;
    }
    if (schema_sd_p != nullptr) {
        *schema_sd_p = nullptr;
    }

    rc = monad_bcap_archive_open_block_fd(
        bca,
        block_number,
#if MONAD_EVENT_USE_O_TMPFILE
        O_RDWR | O_TMPFILE,
#else
        O_RDWR | O_CREAT,
#endif
        dir_create_mode,
        file_create_mode,
        path_buf,
        path_buf_size,
        &block_fd);
    if (rc != 0) {
        return rc;
    }
    rc =
        monad_evcap_writer_create(evcap_writer_p, block_fd, &evcap_writer_opts);
    if (rc != 0) {
        FORMAT_ERRC(
            rc,
            "could not open evcap write for block %lu; caused by:\n%s",
            (unsigned long)block_number,
            monad_evcap_writer_get_last_error());
        goto Error;
    }
    // Add SCHEMA section
    rc = monad_evcap_writer_add_schema_section(
        *evcap_writer_p,
        MONAD_EVENT_CONTENT_TYPE_EXEC,
        g_monad_exec_event_schema_hash,
        &schema_sd);
    if (rc != 0) {
        FORMAT_ERRC(
            rc,
            "could not write SCHEMA section write for block %lu; caused "
            "by:\n%s",
            (unsigned long)block_number,
            monad_evcap_writer_get_last_error());
        goto Error;
    }
    if (schema_sd_p != nullptr) {
        *schema_sd_p = schema_sd;
    }
    if (fd_out != nullptr) {
        *fd_out = block_fd;
    }
    else {
        (void)close(block_fd);
    }
    return 0;

Error:
    monad_evcap_writer_destroy(*evcap_writer_p);
    (void)close(block_fd);
    return rc;
}

int monad_bcap_archive_find_minmax(
    struct monad_bcap_archive const *bca, uint64_t *min_block,
    uint64_t *max_block)
{
    struct scan_dir_result groups_scan;
    struct scan_dir_result min_subdir_scan;
    struct scan_dir_result max_subdir_scan;
    int rc = 0;

    if (min_block == nullptr && max_block == nullptr) {
        // Both outputs are optional, and there's nothing to do
        return 0;
    }

    // memset early so we can unconditionally free(3) the value arrays on error
    memset(&min_subdir_scan, 0, sizeof min_subdir_scan);
    memset(&max_subdir_scan, 0, sizeof max_subdir_scan);
    rc = scan_archive_dir(bca, ST_GROUP_SUBDIRS, 0, &groups_scan);

    // If there's an error, or there are no subdirectories at all, we're done
    if (rc != 0) {
        goto Done;
    }

    // The lowest numbered directories could be empty, thus why this is a loop
    if (min_block != nullptr) {
        for (size_t s = 0; s < groups_scan.len; ++s) {
            uint64_t const subdir = groups_scan.values[s];
            rc =
                scan_archive_dir(bca, ST_BLOCK_FILES, subdir, &min_subdir_scan);
            if (rc != 0) {
                goto Done;
            }
            if (min_subdir_scan.len > 0) {
                break;
            }
            free(min_subdir_scan.values);
        }
        *min_block = min_subdir_scan.min;
    }

    // As above, for the highest-numbered directories
    if (max_block != nullptr) {
        for (size_t s = 0; s < groups_scan.len; ++s) {
            uint64_t const subdir = groups_scan.values[groups_scan.len - s - 1];
            rc =
                scan_archive_dir(bca, ST_BLOCK_FILES, subdir, &max_subdir_scan);
            if (rc != 0) {
                goto Done;
            }
            if (max_subdir_scan.len > 0) {
                break;
            }
            free(max_subdir_scan.values);
        }
        *max_block = max_subdir_scan.max;
    }

Done:
    free(groups_scan.values);
    free(min_subdir_scan.values);
    free(max_subdir_scan.values);
    return rc;
}

int monad_bcap_archive_find_missing(
    struct monad_bcap_archive const *bca, uint64_t min_block,
    uint64_t max_block, struct monad_bcap_block_range_list *missing_ranges)
{
    int rc;
    uint64_t min_subdir;
    uint64_t max_subdir;

    rc = monad_bcap_archive_find_minmax(
        bca,
        min_block == MONAD_BCAP_SEARCH_NO_LIMIT ? &min_block : nullptr,
        max_block == MONAD_BCAP_SEARCH_NO_LIMIT ? &max_block : nullptr);
    if (rc != 0) {
        return rc;
    }
    if (min_block == 0) {
        return 0; // Empty archive; nothing is missing
    }
    if (min_block > max_block) {
        return FORMAT_ERRC(
            EINVAL,
            "min_block %lu > max_block %lu",
            (unsigned long)min_block,
            (unsigned long)max_block);
    }
    min_subdir = block_to_subdir(min_block);
    max_subdir = block_to_subdir(max_block);

    for (uint64_t subdir = min_subdir; subdir <= max_subdir;
         subdir += MONAD_BCAP_ARCHIVE_FILES_PER_SUBDIR) {
        char subdir_buf[32];
        struct stat subdir_stat;
        struct scan_dir_result subdir_scan;
        struct monad_bcap_block_range *last_range;
        bool subdir_missing;
        uint64_t last_block = 0;

        uint64_t const min_missing_in_subdir =
            subdir == min_subdir ? min_block : subdir;
        uint64_t const max_missing_in_subdir =
            subdir == max_subdir
                ? max_block
                : subdir + MONAD_BCAP_ARCHIVE_FILES_PER_SUBDIR - 1;

        sprintf(subdir_buf, "%lu", (unsigned long)subdir);
        rc = fstatat(bca->dirfd, subdir_buf, &subdir_stat, 0);
        if (rc == -1 && errno != ENOENT) {
            rc = FORMAT_ERRC(
                errno, "fstatat(<archive-fd>, %s) failed", subdir_buf);
            goto Error;
        }
        subdir_missing = rc == -1;
        if (!subdir_missing) {
            rc = scan_archive_dir(bca, ST_BLOCK_FILES, subdir, &subdir_scan);
            if (rc != 0) {
                goto Error;
            }
        }
        if (subdir_missing || subdir_scan.len == 0) {
            rc = append_missing_block(
                min_missing_in_subdir, missing_ranges, &last_range);
            if (rc != 0) {
                goto Error;
            }
            last_range->max = max_missing_in_subdir;
            continue;
        }

        if (min_missing_in_subdir < subdir_scan.values[0]) {
            rc = append_missing_block(
                min_missing_in_subdir, missing_ranges, &last_range);
            if (rc != 0) {
                goto Error;
            }
            last_range->max = subdir_scan.values[0] - 1;
        }
        for (size_t s = 0; s < subdir_scan.len; ++s) {
            uint64_t const this_block = subdir_scan.values[s];
            if (this_block < min_block || this_block > max_block) {
                continue;
            }
            if (last_block != 0 && this_block != last_block + 1) {
                // The non-empty range [last_block + 1, this_block) is missing
                rc = append_missing_block(
                    last_block + 1, missing_ranges, &last_range);
                if (rc != 0) {
                    goto Error;
                }
                last_range->max = this_block - 1;
            }
            last_block = this_block;
        }
        if (subdir_scan.values[subdir_scan.len - 1] < max_missing_in_subdir) {
            rc = append_missing_block(
                subdir_scan.values[subdir_scan.len - 1] + 1,
                missing_ranges,
                &last_range);
            if (rc != 0) {
                goto Error;
            }
            last_range->max = max_missing_in_subdir;
        }
    }
    return 0;

Error:
    monad_bcap_block_range_list_free(missing_ranges);
    return rc;
}

void monad_bcap_block_range_list_intersect(
    struct monad_bcap_block_range const *required,
    struct monad_bcap_block_range_list *missing_ranges)
{
    struct monad_bcap_block_range *scan;
    struct monad_bcap_block_range *prev;

    // Remove all missing block segments outside (to the left of) missing_ranges
    scan = TAILQ_FIRST(&missing_ranges->head);
    while (scan != nullptr && scan->max < required->min) {
        prev = scan;
        scan = TAILQ_NEXT(scan, next);
        TAILQ_REMOVE(&missing_ranges->head, prev, next);
        free(prev);
    }

    // If a missing block range straddles `required`, shorten it from the
    // left side to compute the intersection
    if (scan != nullptr && scan->max <= required->max &&
        scan->min < required->min) {
        scan->min = required->min;
        scan = TAILQ_NEXT(scan, next);
    }

    // Skip over any missing block ranges entirely within the
    // `required` range
    while (scan != nullptr && scan->max <= required->max) {
        scan = TAILQ_NEXT(scan, next);
    }

    // The straddle case for the right side
    if (scan != nullptr && scan->min <= required->max &&
        scan->max > required->max) {
        scan->max = required->max;
        scan = TAILQ_NEXT(scan, next);
    }

    // Remove everything after required->max
    while (scan != nullptr) {
        prev = scan;
        scan = TAILQ_NEXT(scan, next);
        TAILQ_REMOVE(&missing_ranges->head, prev, next);
        free(prev);
    }
}
