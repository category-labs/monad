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

#ifndef MONAD_EXEC_ITER_HELP_INTERNAL
    #error This file should only be included directly by exec_iter_help.h
#endif

#include <assert.h>
#include <stdint.h>
#include <string.h>

#include <category/core/event/event_iterator.h>
#include <category/core/event/event_ring.h>
#include <category/core/likely.h>
#include <category/execution/ethereum/core/base_ctypes.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

// Functions like monad_exec_ring_get_block_number expect the caller to pass a
// descriptor containing a consensus event; if this is not the case, we need to
// seek to the nearest BLOCK_START and copy that event into a caller-provided
// buffer, then reseat the event_p pointer to refer to that event buffer instead
static inline bool _monad_exec_ring_ensure_block(
    struct monad_event_ring const *event_ring,
    struct monad_event_descriptor const **event_p,
    struct monad_event_descriptor *buf)
{
    if (MONAD_UNLIKELY(
            (*event_p)->content_ext[MONAD_FLOW_BLOCK_SEQNO] != 0 &&
            (*event_p)->event_type != MONAD_EXEC_BLOCK_START)) {
        if (MONAD_UNLIKELY(!monad_event_ring_try_copy(
                event_ring,
                (*event_p)->content_ext[MONAD_FLOW_BLOCK_SEQNO],
                buf))) {
            return false;
        }
        *event_p = buf;
    }
    return true;
}

// Copy the event descriptor for the consensus event pointed to by `iter`. If
// `iter` is pointing inside a block, rewind it to BLOCK_START, and copy that
// out instead (and set `*moved` to true); if false is returned, the event
// descriptor is not valid
static inline bool _monad_exec_iter_copy_consensus_event(
    struct monad_event_iterator *iter, struct monad_event_descriptor *event,
    bool *moved)
{
    *moved = false;
    if (MONAD_UNLIKELY(
            monad_event_iterator_try_copy(iter, event) !=
            MONAD_EVENT_SUCCESS)) {
        return false;
    }
    if (event->content_ext[MONAD_FLOW_BLOCK_SEQNO] != 0 &&
        event->event_type != MONAD_EXEC_BLOCK_START) {
        uint64_t const iter_save = iter->read_last_seqno;
        monad_event_iterator_set_seqno(
            iter, event->content_ext[MONAD_FLOW_BLOCK_SEQNO]);
        if (MONAD_UNLIKELY(
                monad_event_iterator_try_copy(iter, event) !=
                MONAD_EVENT_SUCCESS)) {
            iter->read_last_seqno = iter_save;
            return false;
        }
        *moved = true;
    }
    return true;
}

static inline bool _monad_exec_ring_is_start_of_block(
    struct monad_event_ring const *event_ring,
    struct monad_event_descriptor const *event, uint64_t block_number)
{
    uint64_t b;
    return event->event_type == MONAD_EXEC_BLOCK_START &&
           monad_exec_ring_get_block_number(event_ring, event, &b) &&
           b == block_number;
}

inline bool monad_exec_ring_get_block_number(
    struct monad_event_ring const *event_ring,
    struct monad_event_descriptor const *event, uint64_t *block_number)
{
    struct monad_event_descriptor buf;
    void const *payload;

    if (MONAD_UNLIKELY(
            !_monad_exec_ring_ensure_block(event_ring, &event, &buf))) {
        return false;
    }

    payload = monad_event_ring_payload_peek(event_ring, event);

    switch (event->event_type) {
    case MONAD_EXEC_BLOCK_START:
        *block_number = ((struct monad_exec_block_start const *)payload)
                            ->block_tag.block_number;
        break;

    case MONAD_EXEC_BLOCK_QC:
        *block_number = ((struct monad_exec_block_qc const *)payload)
                            ->block_tag.block_number;
        break;

    case MONAD_EXEC_BLOCK_FINALIZED:
        *block_number =
            ((struct monad_exec_block_tag const *)payload)->block_number;
        break;

    case MONAD_EXEC_BLOCK_VERIFIED:
        *block_number =
            ((struct monad_exec_block_verified *)payload)->block_number;
        break;

    default:
        return false;
    }

    return monad_event_ring_payload_check(event_ring, event);
}

inline bool monad_exec_ring_block_id_matches(
    struct monad_event_ring const *event_ring,
    struct monad_event_descriptor const *event, monad_c_bytes32 const *block_id)
{
    struct monad_event_descriptor buf;
    void const *payload;
    bool tag_matches;

    if (MONAD_UNLIKELY(
            !_monad_exec_ring_ensure_block(event_ring, &event, &buf))) {
        return false;
    }

    payload = monad_event_ring_payload_peek(event_ring, event);

    switch (event->event_type) {
    case MONAD_EXEC_BLOCK_START:
        tag_matches =
            memcmp(
                block_id,
                &((struct monad_exec_block_start const *)payload)->block_tag.id,
                sizeof *block_id) == 0;
        break;

    case MONAD_EXEC_BLOCK_QC:
        tag_matches =
            memcmp(
                block_id,
                &((struct monad_exec_block_qc const *)payload)->block_tag.id,
                sizeof *block_id) == 0;
        break;

    case MONAD_EXEC_BLOCK_FINALIZED:
        tag_matches = memcmp(
                          block_id,
                          &((struct monad_exec_block_tag const *)payload)->id,
                          sizeof *block_id) == 0;
        break;

    default:
        return false;
    }

    return tag_matches && monad_event_ring_payload_check(event_ring, event);
}

inline bool monad_exec_iter_consensus_prev(
    struct monad_event_iterator *iter, enum monad_exec_event_type filter,
    struct monad_event_descriptor *event)
{
    struct monad_event_descriptor buf;
    bool moved;
    uint64_t const iter_save = iter->read_last_seqno;

    if (event == nullptr) {
        event = &buf;
    }

    // Try to copy out the current consensus event
    if (MONAD_UNLIKELY(
            !_monad_exec_iter_copy_consensus_event(iter, event, &moved))) {
        return false;
    }
    if ((filter == MONAD_EXEC_NONE || filter == MONAD_EXEC_BLOCK_START) &&
        moved) {
        // The above call rewound the iterator from a block-internal event to
        // BLOCK_START; if this happens immediately upon entry and we're
        // interested in stopping at BLOCK_START events, then stop now
        return true;
    }

    // After the above check, if the iterator is valid then it is now pointing
    // at the "current" consensus event. This loop will walk backwards over
    // these type of events, and will stop in the following cases:
    //
    //   - immediately, if filter == MONAD_EXEC_NONE; this means the user
    //     isn't looking for a particular kind of consensus event, and only
    //     wants the immediately previous one
    //
    //   - as soon as filter == event_type, i.e., we find the immediately
    //     previous consensus event type with the given block state, e.g.,
    //     "find the previous BLOCK_FINALIZE"
    //
    // If we run out of events before this occurs, the iterator is reset to
    // its original position, and false is returned
    while (MONAD_UNLIKELY(iter->read_last_seqno > 0)) {
        --iter->read_last_seqno;
        if (MONAD_UNLIKELY(
                !_monad_exec_iter_copy_consensus_event(iter, event, &moved))) {
            break;
        }
        if (filter == MONAD_EXEC_NONE ||
            (uint16_t)filter == event->event_type) {
            return true;
        }
    }

    iter->read_last_seqno = iter_save;
    return false;
}

inline bool monad_exec_iter_block_number_prev(
    struct monad_event_iterator *iter,
    struct monad_event_ring const *event_ring, uint64_t block_number,
    enum monad_exec_event_type filter, struct monad_event_descriptor *event)
{
    uint64_t cur_block_number;
    struct monad_event_descriptor buf;
    uint64_t const iter_save = iter->read_last_seqno;

    switch (filter) {
    case MONAD_EXEC_NONE:
        [[fallthrough]];
    case MONAD_EXEC_BLOCK_START:
        [[fallthrough]];
    case MONAD_EXEC_BLOCK_QC:
        [[fallthrough]];
    case MONAD_EXEC_BLOCK_FINALIZED:
        [[fallthrough]];
    case MONAD_EXEC_BLOCK_VERIFIED:
        break;
    default:
        return false; // Not a valid filter value
    }

    if (event == nullptr) {
        event = &buf;
    }

    while (MONAD_LIKELY(monad_exec_iter_consensus_prev(iter, filter, event))) {
        if (!monad_exec_ring_get_block_number(
                event_ring, event, &cur_block_number)) {
            break;
        }
        if (block_number == cur_block_number) {
            return true;
        }
        if (cur_block_number < block_number &&
            (filter == MONAD_EXEC_BLOCK_FINALIZED ||
             filter == MONAD_EXEC_BLOCK_VERIFIED)) {
            break;
        }
    }

    iter->read_last_seqno = iter_save;
    return false;
}

inline bool monad_exec_iter_block_id_prev(
    struct monad_event_iterator *iter,
    struct monad_event_ring const *event_ring, monad_c_bytes32 const *block_id,
    enum monad_exec_event_type filter, struct monad_event_descriptor *event)
{
    struct monad_event_descriptor buf;
    uint64_t const iter_save = iter->read_last_seqno;

    switch (filter) {
    case MONAD_EXEC_NONE:
        [[fallthrough]];
    case MONAD_EXEC_BLOCK_START:
        [[fallthrough]];
    case MONAD_EXEC_BLOCK_QC:
        [[fallthrough]];
    case MONAD_EXEC_BLOCK_FINALIZED:
        break;
    default:
        return false; // Not a valid filter value
    }

    if (event == nullptr) {
        event = &buf;
    }

    while (MONAD_LIKELY(monad_exec_iter_consensus_prev(iter, filter, event))) {
        if (event->event_type == MONAD_EXEC_BLOCK_VERIFIED) {
            continue;
        }
        if (monad_exec_ring_block_id_matches(event_ring, event, block_id)) {
            return true;
        }
        assert(
            (filter == MONAD_EXEC_BLOCK_START ||
             filter == MONAD_EXEC_BLOCK_QC) &&
            "block number matched, tag didn't, and not START/QC?");
    }

    iter->read_last_seqno = iter_save;
    return false;
}

inline bool monad_exec_iter_rewind_for_simple_replay(
    struct monad_event_iterator *iter,
    struct monad_event_ring const *event_ring, uint64_t block_number,
    struct monad_event_descriptor *event)
{
    uint64_t const iter_save = iter->read_last_seqno;

    // First, scan backwards to find the BLOCK_FINALIZED for block_number
    if (!monad_exec_iter_block_number_prev(
            iter,
            event_ring,
            block_number,
            MONAD_EXEC_BLOCK_FINALIZED,
            event)) {
        return false; // No need to restore iter_save, done by callee
    }

    // There are an unknown number of events (proposed block EVM events,
    // consensus events) between the original proposal of this finalized block
    // and its finalization; the one thing we do know is that once we've seen
    // the BLOCK_START for its original proposal, we want the consensus
    // event immediately prior to that
    bool found_finalized_block_start = false;
    uint64_t prev_read = iter->read_last_seqno;

    while (monad_exec_iter_consensus_prev(iter, MONAD_EXEC_NONE, event) &&
           !(found_finalized_block_start = _monad_exec_ring_is_start_of_block(
                 event_ring, event, block_number))) {
        prev_read = iter->read_last_seqno;
    }

    if (found_finalized_block_start) {
        iter->read_last_seqno = prev_read;
        if (monad_event_iterator_try_copy(iter, event) == MONAD_EVENT_SUCCESS) {
            return true;
        }
    }

    iter->read_last_seqno = iter_save;
    return false;
}
