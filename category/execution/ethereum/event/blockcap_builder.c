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
#include <stdlib.h>
#include <string.h>

#include <category/core/assert.h>
#include <category/core/event/evcap_file.h>
#include <category/core/event/evcap_writer.h>
#include <category/core/event/event_ring.h>
#include <category/core/format_err.h>
#include <category/core/mem/align.h>
#include <category/core/mem/virtual_buf.h>
#include <category/core/srcloc.h>
#include <category/execution/ethereum/event/blockcap.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

thread_local char _g_monad_bcap_error_buf[1024];

#define FORMAT_ERRC(...)                                                       \
    monad_format_err(                                                          \
        _g_monad_bcap_error_buf,                                               \
        sizeof(_g_monad_bcap_error_buf),                                       \
        &MONAD_SOURCE_LOCATION_CURRENT(),                                      \
        __VA_ARGS__)

struct monad_bcap_builder
{
    struct monad_bcap_proposal *current_proposal;
    uint64_t last_exec_seqno;
    struct monad_vbuf_writer *event_vbuf_writer;
    struct monad_vbuf_writer *seqno_index_vbuf_writer;
};

static int builder_append_event(
    struct monad_bcap_builder *bcb, struct monad_event_descriptor const *event,
    void const *payload, enum monad_bcap_append_result *append_result)
{
    int rc;

    if (bcb->current_proposal == nullptr) {
        *append_result = MONAD_BCAP_OUTSIDE_BLOCK_SCOPE;
        return 0;
    }
    size_t const write_offset = monad_round_size_to_align(
        monad_vbuf_writer_get_offset(bcb->event_vbuf_writer),
        alignof(struct monad_event_descriptor));
    rc = monad_evcap_vbuf_append_event(
        bcb->event_vbuf_writer,
        event,
        payload,
        &bcb->current_proposal->event_vbuf_chain);
    if (rc != 0) {
        return FORMAT_ERRC(
            rc,
            "unable to append event %lu to proposal vbuf chain, caused by:\n%s",
            (unsigned long)event->seqno,
            monad_vbuf_writer_get_last_error());
    }
    if (bcb->seqno_index_vbuf_writer != nullptr) {
        rc = monad_vbuf_writer_memcpy(
            bcb->seqno_index_vbuf_writer,
            &write_offset,
            sizeof write_offset,
            alignof(uint64_t),
            &bcb->current_proposal->seqno_index_vbuf_chain);
        if (rc != 0) {
            return FORMAT_ERRC(
                rc,
                "unable to append event %lu to proposal seqno index vbuf, "
                "caused "
                "by:\n%s",
                (unsigned long)event->seqno,
                monad_vbuf_writer_get_last_error());
        }
    }
    if (bcb->current_proposal->event_count++ == 0) {
        bcb->current_proposal->start_seqno = event->seqno;
    }
    *append_result = event->event_type == MONAD_EXEC_BLOCK_START
                         ? MONAD_BCAP_PROPOSAL_CREATED
                         : MONAD_BCAP_PROPOSAL_APPENDED;
    return 0;
}

static int try_create_block_proposal(struct monad_bcap_proposal **proposal_p)
{
    struct monad_bcap_proposal *proposal;
    *proposal_p = proposal = malloc(sizeof *proposal);
    if (proposal == nullptr) {
        return FORMAT_ERRC(errno, "malloc of monad_bcap_proposal failed");
    }
    memset(proposal, 0, sizeof *proposal);
    monad_vbuf_chain_init(&proposal->event_vbuf_chain);
    monad_vbuf_chain_init(&proposal->seqno_index_vbuf_chain);
    return 0;
}

static int act_on_block_start(
    struct monad_bcap_builder *bcb, struct monad_event_descriptor const *event,
    struct monad_exec_block_start const *block_start,
    monad_bcap_append_result_t *append_result,
    struct monad_bcap_proposal **proposal_p)
{
    int rc;

    // It's safe to assert this, because if no sequence number gaps are
    // observed, then we can't see a new BLOCK_START without the previous
    // block being terminated by an event like BLOCK_END or BLOCK_REJECT (unless
    // the state machine of the event system itself is broken)
    MONAD_ASSERT(
        bcb->current_proposal == nullptr,
        "if no gaps, should've been cleared by terminating event");

    if ((rc = try_create_block_proposal(&bcb->current_proposal)) != 0) {
        return rc;
    }
    *proposal_p = bcb->current_proposal;
    bcb->current_proposal->block_tag = block_start->block_tag;
    return builder_append_event(bcb, event, block_start, append_result);
}

static int act_on_block_termination_event(
    struct monad_bcap_builder *bcb, struct monad_event_descriptor const *event,
    void const *payload, enum monad_bcap_append_result *append_result,
    struct monad_bcap_proposal **proposal_p)
{
    int rc = builder_append_event(bcb, event, payload, append_result);
    if (rc != 0) {
        return rc;
    }

    (void)monad_vbuf_writer_reset(
        bcb->event_vbuf_writer, &bcb->current_proposal->event_vbuf_chain);

    if (bcb->seqno_index_vbuf_writer != nullptr) {
        (void)monad_vbuf_writer_reset(
            bcb->seqno_index_vbuf_writer,
            &bcb->current_proposal->seqno_index_vbuf_chain);
    }

    *proposal_p = bcb->current_proposal;
    if (event->event_type == MONAD_EXEC_BLOCK_END) {
        *append_result = MONAD_BCAP_PROPOSAL_FINISHED;
    }
    else {
        // TODO(ken): treat EVM_ERROR differently than BLOCK_REJECT?
        *append_result = MONAD_BCAP_PROPOSAL_ABORTED;
    }
    bcb->current_proposal = nullptr;
    return 0;
}

int monad_bcap_builder_create(
    struct monad_bcap_builder **bcb_p,
    struct monad_vbuf_segment_allocator *event_vbuf_allocator,
    struct monad_vbuf_segment_allocator *seqno_index_vbuf_allocator)
{
    int rc;
    struct monad_bcap_builder *bcb = *bcb_p = malloc(sizeof *bcb);
    if (bcb == nullptr) {
        return FORMAT_ERRC(errno, "malloc of monad_bcap_builder failed");
    }
    memset(bcb, 0, sizeof *bcb);
    rc =
        monad_vbuf_writer_create(&bcb->event_vbuf_writer, event_vbuf_allocator);
    if (rc != 0) {
        FORMAT_ERRC(
            rc,
            "blockcap builder event vbuf writer create failed; caused by:\n%s",
            monad_vbuf_writer_get_last_error());
        goto Error;
    }
    if (seqno_index_vbuf_allocator != nullptr) {
        rc = monad_vbuf_writer_create(
            &bcb->seqno_index_vbuf_writer, seqno_index_vbuf_allocator);
        if (rc != 0) {
            FORMAT_ERRC(
                rc,
                "blockcap builder seqno index vbuf writer create failed; "
                "caused by:\n%s",
                monad_vbuf_writer_get_last_error());
            goto Error;
        }
    }
    return 0;

Error:
    monad_bcap_builder_destroy(bcb);
    *bcb_p = nullptr;
    return rc;
}

void monad_bcap_builder_destroy(struct monad_bcap_builder *bcb)
{
    if (bcb != nullptr) {
        struct monad_vbuf_chain flush_chain;
        monad_vbuf_chain_init(&flush_chain);
        monad_bcap_proposal_free(bcb->current_proposal);
        monad_vbuf_writer_destroy(bcb->event_vbuf_writer, &flush_chain);
        monad_vbuf_writer_destroy(bcb->seqno_index_vbuf_writer, &flush_chain);
        monad_vbuf_chain_free(&flush_chain);
        free(bcb);
    }
}

struct monad_bcap_proposal *
monad_bcap_builder_get_current_proposal(struct monad_bcap_builder const *bcb)
{
    return bcb->current_proposal;
}

int monad_bcap_builder_append_event(
    struct monad_bcap_builder *bcb, struct monad_event_descriptor const *event,
    void const *payload, monad_bcap_append_result_t *append_result,
    struct monad_bcap_proposal **proposal_p)
{
    *append_result = MONAD_BCAP_ERROR;
    *proposal_p = nullptr;

    if (bcb->last_exec_seqno > 0 && event->seqno != bcb->last_exec_seqno + 1) {
        return FORMAT_ERRC(
            EILSEQ,
            "sequence number gap in exec ring "
            "%lu -> %lu, block writer desync",
            (unsigned long)bcb->last_exec_seqno,
            (unsigned long)event->seqno);
    }
    bcb->last_exec_seqno = event->seqno;

    if (event->content_ext[MONAD_FLOW_BLOCK_SEQNO] == 0) {
        // Not a block-related event; we don't process these
        *append_result = MONAD_BCAP_OUTSIDE_BLOCK_SCOPE;
        return 0;
    }
    if (bcb->current_proposal == nullptr &&
        event->event_type != MONAD_EXEC_BLOCK_START) {
        // Not currently within a block boundary, and not starting a new block
        // either; this happens when we start seeing events in the middle of a
        // proposal's execution; we just ignore these
        *append_result = MONAD_BCAP_OUTSIDE_BLOCK_SCOPE;
        return 0;
    }

    switch (event->event_type) {
    case MONAD_EXEC_BLOCK_START:
        return act_on_block_start(
            bcb,
            event,
            (struct monad_exec_block_start const *)payload,
            append_result,
            proposal_p);

    case MONAD_EXEC_EVM_ERROR:
        [[fallthrough]];
    case MONAD_EXEC_BLOCK_REJECT:
        [[fallthrough]];
    case MONAD_EXEC_BLOCK_END:
        return act_on_block_termination_event(
            bcb, event, payload, append_result, proposal_p);

    default:
        *proposal_p = bcb->current_proposal;
        return builder_append_event(bcb, event, payload, append_result);
    }
}

void monad_bcap_builder_reset(struct monad_bcap_builder *bcb)
{
    if (bcb->current_proposal) {
        (void)monad_vbuf_writer_reset(
            bcb->event_vbuf_writer, &bcb->current_proposal->event_vbuf_chain);
        if (bcb->seqno_index_vbuf_writer != nullptr) {
            (void)monad_vbuf_writer_reset(
                bcb->seqno_index_vbuf_writer,
                &bcb->current_proposal->seqno_index_vbuf_chain);
        }
        monad_bcap_proposal_free(bcb->current_proposal);
        bcb->current_proposal = nullptr;
    }
    bcb->last_exec_seqno = 0;
}

void monad_bcap_proposal_free(struct monad_bcap_proposal *proposal)
{
    if (proposal != nullptr) {
        monad_vbuf_chain_free(&proposal->event_vbuf_chain);
        monad_vbuf_chain_free(&proposal->seqno_index_vbuf_chain);
        free(proposal);
    }
}

char const *monad_bcap_get_last_error()
{
    return _g_monad_bcap_error_buf;
}
