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

#include <category/core/assert.h>
#include <category/core/format_err.h>
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

struct monad_bcap_finalize_tracker
{
    struct monad_bcap_proposal_list pending;
};

int monad_bcap_finalize_tracker_create(
    struct monad_bcap_finalize_tracker **ft_p)
{
    *ft_p = malloc(sizeof **ft_p);
    if (*ft_p == nullptr) {
        return FORMAT_ERRC(
            errno, "malloc of monad_bcap_finalize_tracker_create failed");
    }
    TAILQ_INIT(&(*ft_p)->pending);
    return 0;
}

void monad_bcap_finalize_tracker_destroy(struct monad_bcap_finalize_tracker *ft)
{
    if (ft != nullptr) {
        monad_bcap_finalize_tracker_reset(ft);
        free(ft);
    }
}

void monad_bcap_finalize_tracker_add_proposal(
    struct monad_bcap_finalize_tracker *ft,
    struct monad_bcap_proposal *proposal)
{
    TAILQ_INSERT_TAIL(&ft->pending, proposal, entry);
}

int monad_bcap_finalize_tracker_update(
    struct monad_bcap_finalize_tracker *ft,
    struct monad_exec_block_tag const *block_tag,
    struct monad_bcap_proposal **finalized,
    struct monad_bcap_proposal_list *abandoned)
{
    *finalized = nullptr;
    TAILQ_INIT(abandoned);

    struct monad_bcap_proposal *scan = TAILQ_FIRST(&ft->pending);
    while (scan != nullptr) {
        if (scan->block_tag.block_number > block_tag->block_number) {
            // Proposal is for a later block than the finalized block height;
            // skip it
            scan = TAILQ_NEXT(scan, entry);
            continue;
        }
        if (scan->block_tag.block_number != block_tag->block_number) {
            return FORMAT_ERRC(
                ENOTRECOVERABLE,
                "unfinalized proposal for block %lu [%lx] present during "
                "finalization of %lu [%lx]",
                (unsigned long)scan->block_tag.block_number,
                *(unsigned long const *)scan->block_tag.id.bytes,
                (unsigned long)block_tag->block_number,
                *(unsigned long const *)block_tag->id.bytes);
        }

        // This proposal has the same block number as the finalization event;
        // remove it from the pending list, it will either be finalized or
        // abandoned
        MONAD_DEBUG_ASSERT(
            scan->block_tag.block_number == block_tag->block_number);
        TAILQ_REMOVE(&ft->pending, scan, entry);

        if (memcmp(
                &scan->block_tag.id,
                &block_tag->id,
                sizeof scan->block_tag.id) == 0) {
            scan->is_finalized = true;
            *finalized = scan;
        }
        else {
            TAILQ_INSERT_TAIL(abandoned, scan, entry);
        }

        scan = TAILQ_FIRST(&ft->pending);
    }

    return 0;
}

void monad_bcap_finalize_tracker_reset(struct monad_bcap_finalize_tracker *ft)
{
    struct monad_bcap_proposal *p;
    while ((p = TAILQ_FIRST(&ft->pending))) {
        TAILQ_REMOVE(&ft->pending, p, entry);
        monad_bcap_proposal_free(p);
    }
}
