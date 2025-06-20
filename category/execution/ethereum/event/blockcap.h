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
 * This file defines utilities used with the event capture ("evcap") system,
 * for writing block-oriented capture files. They are called the "block
 * capture" (blockcap or "bcap") utilities.
 */

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <sys/queue.h>
#include <sys/types.h>

#include <category/core/mem/virtual_buf.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

#ifdef __cplusplus
extern "C"
{
#endif

enum monad_exec_event_type : uint16_t;

enum monad_evcap_section_compression : uint8_t;

struct monad_evcap_reader;
struct monad_evcap_section_desc;
struct monad_evcap_writer;
struct monad_event_descriptor;
struct monad_vbuf_segment_allocator;

typedef struct ZSTD_CCtx_s ZSTD_CCtx;

/// This object represents the "recorded form" of a proposed block's execution.
///
/// It contains:
///
///    - The block number and ID of the proposed block
///
///    - A vbuf chain holding all the events associated with the proposal's
///      execution, recorded in the event capture format
///
/// Note that this object, which records the events in a "proposed block",
/// has a different meaning than the word "proposal" in the consensus
/// algorithm. There, it refers to an attempt to vote on a particular block, in
/// a particular round; here it means "a block which is not yet finalized".
struct monad_bcap_proposal
{
    struct monad_exec_block_tag block_tag;
    size_t event_count;
    uint64_t start_seqno;
    struct monad_vbuf_chain event_vbuf_chain;
    struct monad_vbuf_chain seqno_index_vbuf_chain;
    bool is_finalized;
    void *user;
    TAILQ_ENTRY(monad_bcap_proposal) entry;
};

void monad_bcap_proposal_free(struct monad_bcap_proposal *);

TAILQ_HEAD(monad_bcap_proposal_list, monad_bcap_proposal);

/*
 * monad_bcap_builder
 *
 * This API is used to build `struct monad_bcap_proposal` objects, which
 * are vbuf chains holding all recorded events in the scope of a proposal
 */

typedef enum monad_bcap_append_result
{
    MONAD_BCAP_ERROR,
    MONAD_BCAP_OUTSIDE_BLOCK_SCOPE,
    MONAD_BCAP_PROPOSAL_CREATED,
    MONAD_BCAP_PROPOSAL_APPENDED,
    MONAD_BCAP_PROPOSAL_FINISHED,
    MONAD_BCAP_PROPOSAL_ABORTED,
} monad_bcap_append_result_t;

struct monad_bcap_builder;

int monad_bcap_builder_create(
    struct monad_bcap_builder **,
    struct monad_vbuf_segment_allocator *event_vbuf_allocator,
    struct monad_vbuf_segment_allocator *seqno_index_vbuf_allocator);

void monad_bcap_builder_destroy(struct monad_bcap_builder *);

struct monad_bcap_proposal *
monad_bcap_builder_get_current_proposal(struct monad_bcap_builder const *);

int monad_bcap_builder_append_event(
    struct monad_bcap_builder *, struct monad_event_descriptor const *,
    void const *payload, monad_bcap_append_result_t *,
    struct monad_bcap_proposal **);

void monad_bcap_builder_reset(struct monad_bcap_builder *);

/*
 * monad_bcap_finalize_tracker
 *
 * This API tracks when block proposals are finalized or abandoned, based on
 * consensus events
 */

struct monad_bcap_finalize_tracker;

int monad_bcap_finalize_tracker_create(struct monad_bcap_finalize_tracker **);

void monad_bcap_finalize_tracker_destroy(struct monad_bcap_finalize_tracker *);

void monad_bcap_finalize_tracker_add_proposal(
    struct monad_bcap_finalize_tracker *, struct monad_bcap_proposal *);

int monad_bcap_finalize_tracker_update(
    struct monad_bcap_finalize_tracker *,
    struct monad_exec_block_tag const *block_tag,
    struct monad_bcap_proposal **finalized,
    struct monad_bcap_proposal_list *abandoned);

void monad_bcap_finalize_tracker_reset(struct monad_bcap_finalize_tracker *);

/*
 * monad_bcap_pack_writer
 *
 * This API defines a layer on top of the "evcap" (event capture) file format
 * which records a block capture "pack" file, which adds in simple indexing and
 * metadata about block boundaries for recording execution rings.
 *
 * A pack file is just a regular event capture file with:
 *
 *   - Multiple EVENT_BUNDLE sections in it, with one section containing all
 *     the events for a particular finalized block
 *
 *   - A PACK_INDEX section that describes the finalized block number -> event
 *     bundle section mapping. It is designed to be mmap'ed with MAP_SHARED and
 *     is updated atomically for readers that are "polling" the finalized block
 *     index during recovery
 *
 * It is used for producing multi-block analysis in a single file, and is
 * typically used for performance analysis
 */

struct monad_bcap_pack_writer;

int monad_bcap_pack_writer_create(
    struct monad_bcap_pack_writer **, int fd, unsigned max_sections);

void monad_bcap_pack_writer_destroy(struct monad_bcap_pack_writer *);

struct monad_evcap_writer *
monad_bcap_pack_writer_get_evcap_writer(struct monad_bcap_pack_writer *);

int monad_bcap_pack_writer_add_block(
    struct monad_bcap_pack_writer *, struct monad_bcap_proposal const *,
    ZSTD_CCtx *event_zstd_cctx, ZSTD_CCtx *seqno_index_zstd_cctx);

/*
 * monad_bcap_archive
 *
 * This API is used to read and write finalized blocks into a directory
 * structure called the (local) finalized block archive (or "FBA")
 */

struct monad_bcap_archive;

constexpr uint64_t MONAD_BCAP_ARCHIVE_FILES_PER_SUBDIR = 10'000;

constexpr uint64_t MONAD_BCAP_SEARCH_NO_LIMIT = 0;

struct monad_bcap_block_range
{
    uint64_t min;
    uint64_t max;
    TAILQ_ENTRY(monad_bcap_block_range) next;
};

TAILQ_HEAD(monad_bcap_block_range_head, monad_bcap_block_range);

struct monad_bcap_block_range_list
{
    struct monad_bcap_block_range_head head;
    size_t num_segments;
};

int monad_bcap_archive_open(
    struct monad_bcap_archive **, int dirfd, char const *error_name);

void monad_bcap_archive_close(struct monad_bcap_archive *);

int monad_bcap_archive_get_dirfd(struct monad_bcap_archive const *);

int monad_bcap_archive_format_block_path(
    uint64_t block_number, char *path_buf, size_t path_buf_size,
    char const **subdir_end);

int monad_bcap_archive_open_block_fd(
    struct monad_bcap_archive const *, uint64_t block_number, int open_flags,
    mode_t dir_create_mode, mode_t file_create_mode, char *path_buf,
    size_t path_buf_size, int *fd_out);

int monad_bcap_archive_open_block_reader(
    struct monad_bcap_archive const *, uint64_t block_number, char *path_buf,
    size_t path_buf_size, int *fd_out, struct monad_evcap_reader **,
    struct monad_evcap_section_desc const **);

int monad_bcap_archive_open_block_writer(
    struct monad_bcap_archive *, uint64_t block_number, mode_t dir_create_mode,
    mode_t file_create_mode, char *path_buf, size_t path_buf_size, int *fd_out,
    struct monad_evcap_writer **, struct monad_evcap_section_desc const **);

int monad_bcap_archive_close_block_writer(
    struct monad_bcap_archive *, uint64_t block_number,
    struct monad_evcap_writer *, char const *path_buf);

int monad_bcap_archive_find_minmax(
    struct monad_bcap_archive const *, uint64_t *min_block,
    uint64_t *max_block);

int monad_bcap_archive_find_missing(
    struct monad_bcap_archive const *, uint64_t min_block, uint64_t max_block,
    struct monad_bcap_block_range_list *missing_ranges);

void monad_bcap_block_range_list_intersect(
    struct monad_bcap_block_range const *required,
    struct monad_bcap_block_range_list *missing_ranges);

[[gnu::always_inline]] static inline void
monad_bcap_block_range_list_init(struct monad_bcap_block_range_list *list)
{
    memset(list, 0, sizeof *list);
    TAILQ_INIT(&list->head);
}

[[gnu::always_inline]] static inline void
monad_bcap_block_range_list_free(struct monad_bcap_block_range_list *list)
{
    if (list != nullptr) {
        struct monad_bcap_block_range *r;
        while ((r = TAILQ_FIRST(&list->head)) != nullptr) {
            TAILQ_REMOVE(&list->head, r, next);
            free(r);
        }
    }
}

/*
 * Shared functions
 */

int monad_bcap_write_proposal_evcap_ext(
    struct monad_evcap_writer *, struct monad_bcap_proposal const *proposal,
    struct monad_evcap_section_desc const *schema_sd,
    struct monad_evcap_section_desc **event_sd,
    struct monad_evcap_section_desc **seqno_index_sd,
    ZSTD_CCtx *event_zstd_cctx, ZSTD_CCtx *seqno_index_zstd_cctx);

/// Return a description of the last block capture API error that occurred on
/// this thread
char const *monad_bcap_get_last_error();

struct monad_bcap_pack_index_entry
{
    alignas(16) uint64_t block_number;
    uint64_t section_desc_offset;
};

// This must be a power of 2, so that an integral number of them fit into an
// mmap'ed page
static_assert(sizeof(struct monad_bcap_pack_index_entry) == 16);

#ifdef __cplusplus
} // extern "C"
#endif
