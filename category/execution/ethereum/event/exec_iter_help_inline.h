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

#include <category/core/event/event_ring.h>
#include <category/core/event/event_source.h>
#include <category/core/likely.h>
#include <category/execution/ethereum/core/base_ctypes.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

// Functions like monad_exec_get_block_number expect the caller to pass a
// descriptor containing a consensus event; if this is not the case, we need to
// seek to the nearest BLOCK_START and copy that event into a caller-provided
// buffer, then reseat the event_p pointer to refer to that event buffer instead
static inline bool _monad_exec_ensure_block(
    void const *source, struct monad_event_descriptor const **event_p,
    void const **payload, struct monad_event_descriptor *buf,
    struct monad_evsrc_ops const *source_ops)
{
    if (MONAD_UNLIKELY(
            (*event_p)->content_ext[MONAD_FLOW_BLOCK_SEQNO] != 0 &&
            (*event_p)->event_type != MONAD_EXEC_BLOCK_START)) {
        if (MONAD_UNLIKELY(
                source_ops->copy_seqno(
                    source,
                    (*event_p)->content_ext[MONAD_FLOW_BLOCK_SEQNO],
                    buf,
                    payload) != MONAD_EVSRC_SUCCESS)) {
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
    void *iter, struct monad_event_descriptor *event, void const **payload,
    bool *moved, struct monad_evsrc_iter_ops const *iter_ops)
{
    *moved = false;
    if (MONAD_UNLIKELY(
            iter_ops->try_copy(iter, event, nullptr) != MONAD_EVSRC_SUCCESS)) {
        return false;
    }
    if (event->content_ext[MONAD_FLOW_BLOCK_SEQNO] != 0 &&
        event->event_type != MONAD_EXEC_BLOCK_START) {
        uint64_t const iter_save = iter_ops->tell(iter);
        if (MONAD_UNLIKELY(
                iter_ops->set_seqno(
                    iter, event->content_ext[MONAD_FLOW_BLOCK_SEQNO]) !=
                MONAD_EVSRC_SUCCESS)) {
            return false;
        }
        if (MONAD_UNLIKELY(
                iter_ops->try_copy(iter, event, payload) !=
                MONAD_EVSRC_SUCCESS)) {
            iter_ops->seek(iter, iter_save);
            return false;
        }
        *moved = true;
    }
    return true;
}

/*
 * monad_exec_get_block_number
 */

static inline bool monad_exec_get_block_number_generic(
    void const *source, struct monad_event_descriptor const *event,
    void const *payload, uint64_t *block_number,
    struct monad_evsrc_ops const *source_ops)
{
    struct monad_event_descriptor buf;

    if (MONAD_UNLIKELY(!_monad_exec_ensure_block(
            source, &event, &payload, &buf, source_ops))) {
        return false;
    }

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

    return source_ops->check_payload(source, event);
}

inline bool monad_exec_get_block_number_r(
    struct monad_event_ring const *event_ring,
    struct monad_event_descriptor const *event, void const *payload,
    uint64_t *block_number)
{
    MONAD_DEFINE_EVSRC_OPS(source_ops, r)
    return monad_exec_get_block_number_generic(
        event_ring, event, payload, block_number, &source_ops);
}

inline bool monad_exec_get_block_number_c(
    struct monad_evcap_event_section const *event_section,
    struct monad_event_descriptor const *event, void const *payload,
    uint64_t *block_number)
{
    MONAD_DEFINE_EVSRC_OPS(source_ops, c)
    return monad_exec_get_block_number_generic(
        event_section, event, payload, block_number, &source_ops);
}

inline bool monad_exec_get_block_number_a(
    struct monad_evsrc_any const *any,
    struct monad_event_descriptor const *event, void const *payload,
    uint64_t *block_number)
{
    MONAD_DEFINE_EVSRC_OPS(source_ops, a)
    return monad_exec_get_block_number_generic(
        any, event, payload, block_number, &source_ops);
}

/*
 * monad_exec_get_block_id
 */

static inline bool monad_exec_get_block_id_generic(
    void const *source, struct monad_event_descriptor const *event,
    void const *payload, monad_c_bytes32 *block_id,
    struct monad_evsrc_ops const *source_ops)
{
    struct monad_event_descriptor buf;

    if (MONAD_UNLIKELY(!_monad_exec_ensure_block(
            source, &event, &payload, &buf, source_ops))) {
        return false;
    }

    switch (event->event_type) {
    case MONAD_EXEC_BLOCK_START:
        *block_id =
            ((struct monad_exec_block_start const *)payload)->block_tag.id;
        break;

    case MONAD_EXEC_BLOCK_QC:
        *block_id = ((struct monad_exec_block_qc const *)payload)->block_tag.id;
        break;

    case MONAD_EXEC_BLOCK_FINALIZED:
        *block_id = ((struct monad_exec_block_tag const *)payload)->id;
        break;

    default:
        return false;
    }

    return source_ops->check_payload(source, event);
}

inline bool monad_exec_get_block_id_r(
    struct monad_event_ring const *event_ring,
    struct monad_event_descriptor const *event, void const *payload,
    monad_c_bytes32 *block_id)
{
    MONAD_DEFINE_EVSRC_OPS(source_ops, r)
    return monad_exec_get_block_id_generic(
        event_ring, event, payload, block_id, &source_ops);
}

inline bool monad_exec_get_block_id_c(
    struct monad_evcap_event_section const *event_section,
    struct monad_event_descriptor const *event, void const *payload,
    monad_c_bytes32 *block_id)
{
    MONAD_DEFINE_EVSRC_OPS(source_ops, c)
    return monad_exec_get_block_id_generic(
        event_section, event, payload, block_id, &source_ops);
}

inline bool monad_exec_get_block_id_a(
    struct monad_evsrc_any const *any,
    struct monad_event_descriptor const *event, void const *payload,
    monad_c_bytes32 *block_id)
{
    MONAD_DEFINE_EVSRC_OPS(source_ops, a)
    return monad_exec_get_block_id_generic(
        any, event, payload, block_id, &source_ops);
}

/*
 * monad_exec_iter_consensus_prev
 */

static inline bool monad_exec_iter_consensus_prev_generic(
    void *iter, enum monad_exec_event_type filter,
    struct monad_event_descriptor *event, void const **payload,
    struct monad_evsrc_iter_ops const *iter_ops)
{
    struct monad_event_descriptor event_buf;
    void const *payload_buf;
    bool moved;
    uint64_t const iter_save = iter_ops->tell(iter);

    if (event == nullptr) {
        event = &event_buf;
    }
    if (payload == nullptr) {
        payload = &payload_buf;
    }

    // Try to copy out the current consensus event
    if (MONAD_UNLIKELY(!_monad_exec_iter_copy_consensus_event(
            iter, event, payload, &moved, iter_ops))) {
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
    while (MONAD_UNLIKELY(
        iter_ops->try_prev(iter, event, payload) == MONAD_EVSRC_SUCCESS)) {
        if (MONAD_UNLIKELY(!_monad_exec_iter_copy_consensus_event(
                iter, event, payload, &moved, iter_ops))) {
            break;
        }
        if (filter == MONAD_EXEC_NONE ||
            (uint16_t)filter == event->event_type) {
            return true;
        }
    }

    iter_ops->seek(iter, iter_save);
    return false;
}

inline bool monad_exec_iter_consensus_prev_ri(
    struct monad_event_ring_iter *iter, enum monad_exec_event_type filter,
    struct monad_event_descriptor *event, void const **payload)
{
    MONAD_DEFINE_EVSRC_ITER_OPS(iter_ops, r)
    return monad_exec_iter_consensus_prev_generic(
        iter, filter, event, payload, &iter_ops);
}

inline bool monad_exec_iter_consensus_prev_ci(
    struct monad_evcap_event_iter *iter, enum monad_exec_event_type filter,
    struct monad_event_descriptor *event, void const **payload)
{
    MONAD_DEFINE_EVSRC_ITER_OPS(iter_ops, c)
    return monad_exec_iter_consensus_prev_generic(
        iter, filter, event, payload, &iter_ops);
}

inline bool monad_exec_iter_consensus_prev_ai(
    struct monad_evsrc_any_iter *iter, enum monad_exec_event_type filter,
    struct monad_event_descriptor *event, void const **payload)
{
    MONAD_DEFINE_EVSRC_ITER_OPS(iter_ops, a)
    return monad_exec_iter_consensus_prev_generic(
        iter, filter, event, payload, &iter_ops);
}

/*
 * monad_exec_iter_block_number_prev
 */

static inline bool monad_exec_iter_block_number_prev_generic(
    void const *source, void *iter, uint64_t block_number,
    enum monad_exec_event_type filter, struct monad_event_descriptor *event,
    void const **payload, struct monad_evsrc_ops const *source_ops,
    struct monad_evsrc_iter_ops const *iter_ops)
{
    uint64_t cur_block_number;
    struct monad_event_descriptor event_buf;
    void const *payload_buf;
    uint64_t const iter_save = iter_ops->tell(iter);

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
        event = &event_buf;
    }
    if (payload == nullptr) {
        payload = &payload_buf;
    }

    while (MONAD_LIKELY(monad_exec_iter_consensus_prev_generic(
        iter, filter, event, payload, iter_ops))) {
        if (!monad_exec_get_block_number_generic(
                source, event, *payload, &cur_block_number, source_ops)) {
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

    iter_ops->seek(iter, iter_save);
    return false;
}

inline bool monad_exec_iter_block_number_prev_ri(
    struct monad_event_ring_iter *iter, uint64_t block_number,
    enum monad_exec_event_type filter, struct monad_event_descriptor *event,
    void const **payload)
{
    MONAD_DEFINE_EVSRC_OPS(source_ops, r)
    MONAD_DEFINE_EVSRC_ITER_OPS(iter_ops, r)
    return monad_exec_iter_block_number_prev_generic(
        iter->event_ring,
        iter,
        block_number,
        filter,
        event,
        payload,
        &source_ops,
        &iter_ops);
}

inline bool monad_exec_iter_block_number_prev_ci(
    struct monad_evcap_event_iter *iter, uint64_t block_number,
    enum monad_exec_event_type filter, struct monad_event_descriptor *event,
    void const **payload)
{
    MONAD_DEFINE_EVSRC_OPS(source_ops, c)
    MONAD_DEFINE_EVSRC_ITER_OPS(iter_ops, c)
    return monad_exec_iter_block_number_prev_generic(
        iter->event_section,
        iter,
        block_number,
        filter,
        event,
        payload,
        &source_ops,
        &iter_ops);
}

inline bool monad_exec_iter_block_number_prev_ai(
    struct monad_evsrc_any_iter *iter, uint64_t block_number,
    enum monad_exec_event_type filter, struct monad_event_descriptor *event,
    void const **payload)
{
    MONAD_DEFINE_EVSRC_OPS(source_ops, a)
    MONAD_DEFINE_EVSRC_ITER_OPS(iter_ops, a)
    return monad_exec_iter_block_number_prev_generic(
        monad_evsrc_any_from_aci(iter),
        iter,
        block_number,
        filter,
        event,
        payload,
        &source_ops,
        &iter_ops);
}

/*
 * monad_exec_iter_block_id_prev
 */

static inline bool monad_exec_iter_block_id_prev_generic(
    void const *source, void *iter, monad_c_bytes32 const *target_block_id,
    enum monad_exec_event_type filter, struct monad_event_descriptor *event,
    void const **payload, struct monad_evsrc_ops const *source_ops,
    struct monad_evsrc_iter_ops const *iter_ops)
{
    struct monad_event_descriptor event_buf;
    void const *payload_buf;
    monad_c_bytes32 block_id_buf;
    uint64_t const iter_save = iter_ops->tell(iter);

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
        event = &event_buf;
    }
    if (payload == nullptr) {
        payload = &payload_buf;
    }

    while (MONAD_LIKELY(monad_exec_iter_consensus_prev_generic(
        iter, filter, event, payload, iter_ops))) {
        if (event->event_type == MONAD_EXEC_BLOCK_VERIFIED) {
            continue;
        }
        if (!monad_exec_get_block_id_generic(
                source, event, *payload, &block_id_buf, source_ops)) {
            return false;
        }
        if (memcmp(&block_id_buf, target_block_id, sizeof block_id_buf) == 0) {
            return true;
        }
        assert(
            (filter == MONAD_EXEC_BLOCK_START ||
             filter == MONAD_EXEC_BLOCK_QC) &&
            "block number matched, tag didn't, and not START/QC?");
    }

    iter_ops->seek(iter, iter_save);
    return false;
}

inline bool monad_exec_iter_block_id_prev_ri(
    struct monad_event_ring_iter *iter, monad_c_bytes32 const *target_block_id,
    enum monad_exec_event_type filter, struct monad_event_descriptor *event,
    void const **payload)
{
    MONAD_DEFINE_EVSRC_OPS(source_ops, r)
    MONAD_DEFINE_EVSRC_ITER_OPS(iter_ops, r)
    return monad_exec_iter_block_id_prev_generic(
        iter->event_ring,
        iter,
        target_block_id,
        filter,
        event,
        payload,
        &source_ops,
        &iter_ops);
}

inline bool monad_exec_iter_block_id_prev_ci(
    struct monad_evcap_event_iter *iter, monad_c_bytes32 const *target_block_id,
    enum monad_exec_event_type filter, struct monad_event_descriptor *event,
    void const **payload)
{
    MONAD_DEFINE_EVSRC_OPS(source_ops, c)
    MONAD_DEFINE_EVSRC_ITER_OPS(iter_ops, c)
    return monad_exec_iter_block_id_prev_generic(
        iter->event_section,
        iter,
        target_block_id,
        filter,
        event,
        payload,
        &source_ops,
        &iter_ops);
}

inline bool monad_exec_iter_block_id_prev_ai(
    struct monad_evsrc_any_iter *iter, monad_c_bytes32 const *target_block_id,
    enum monad_exec_event_type filter, struct monad_event_descriptor *event,
    void const **payload)
{
    MONAD_DEFINE_EVSRC_OPS(source_ops, a)
    MONAD_DEFINE_EVSRC_ITER_OPS(iter_ops, a)
    return monad_exec_iter_block_id_prev_generic(
        monad_evsrc_any_from_aci(iter),
        iter,
        target_block_id,
        filter,
        event,
        payload,
        &source_ops,
        &iter_ops);
}

static inline bool _monad_exec_is_start_of_block(
    void const *source, struct monad_event_descriptor const *event,
    void const *payload, uint64_t block_number,
    struct monad_evsrc_ops const *source_ops)
{
    uint64_t b;
    return event->event_type == MONAD_EXEC_BLOCK_START &&
           monad_exec_get_block_number_generic(
               source, event, payload, &b, source_ops) &&
           b == block_number;
}

/*
 * monad_exec_iter_rewind_for_simple_replay
 */

static inline bool monad_exec_iter_rewind_for_simple_replay_generic(
    void const *source, void *iter, uint64_t block_number,
    struct monad_event_descriptor *event, void const **payload,
    struct monad_evsrc_ops const *source_ops,
    struct monad_evsrc_iter_ops const *iter_ops)
{
    struct monad_event_descriptor event_buf;
    void const *payload_buf;
    uint64_t cur_block_number;
    uint64_t const iter_save = iter_ops->tell(iter);

    if (event == nullptr) {
        event = &event_buf;
    }
    if (payload == nullptr) {
        payload = &payload_buf;
    }

    // Check if the event the iterator is currently pointing to is already the
    // BLOCK_FINALIZED event we're looking for; in that case we won't scan
    // backwards in the stream to look for it
    bool const can_skip_finalized_seek =
        iter_ops->try_copy(iter, event, payload) == MONAD_EVSRC_SUCCESS &&
        event->event_type == MONAD_EXEC_BLOCK_FINALIZED &&
        monad_exec_get_block_number_generic(
            source, event, *payload, &cur_block_number, source_ops) &&
        cur_block_number == block_number;

    // First, scan backwards to find the BLOCK_FINALIZED for block_number
    if (!can_skip_finalized_seek && !monad_exec_iter_block_number_prev_generic(
                                        source,
                                        iter,
                                        block_number,
                                        MONAD_EXEC_BLOCK_FINALIZED,
                                        event,
                                        payload,
                                        source_ops,
                                        iter_ops)) {
        return false; // No need to restore iter_save, done by callee
    }

    // There are an unknown number of events (proposed block EVM events,
    // consensus events) between the original proposal of this finalized block
    // and its finalization; the one thing we do know is that once we've seen
    // the BLOCK_START for its original proposal, we want the consensus
    // event immediately prior to that
    bool found_finalized_block_start = false;
    uint64_t prev_read = iter_ops->tell(iter);

    while (monad_exec_iter_consensus_prev_generic(
               iter, MONAD_EXEC_NONE, event, payload, iter_ops) &&
           !(found_finalized_block_start = _monad_exec_is_start_of_block(
                 source, event, *payload, block_number, source_ops))) {
        prev_read = iter_ops->tell(iter);
    }

    if (found_finalized_block_start) {
        iter_ops->seek(iter, prev_read);
        if (iter_ops->try_copy(iter, event, payload) == MONAD_EVSRC_SUCCESS) {
            return true;
        }
    }

    iter_ops->seek(iter, iter_save);
    return false;
}

inline bool monad_exec_iter_rewind_for_simple_replay_ri(
    struct monad_event_ring_iter *iter, uint64_t block_number,
    struct monad_event_descriptor *event, void const **payload)
{
    MONAD_DEFINE_EVSRC_OPS(source_ops, r)
    MONAD_DEFINE_EVSRC_ITER_OPS(iter_ops, r)
    return monad_exec_iter_rewind_for_simple_replay_generic(
        iter->event_ring,
        iter,
        block_number,
        event,
        payload,
        &source_ops,
        &iter_ops);
}

inline bool monad_exec_iter_rewind_for_simple_replay_ci(
    struct monad_evcap_event_iter *iter, uint64_t block_number,
    struct monad_event_descriptor *event, void const **payload)
{
    MONAD_DEFINE_EVSRC_OPS(source_ops, c)
    MONAD_DEFINE_EVSRC_ITER_OPS(iter_ops, c)
    return monad_exec_iter_rewind_for_simple_replay_generic(
        iter->event_section,
        iter,
        block_number,
        event,
        payload,
        &source_ops,
        &iter_ops);
}

inline bool monad_exec_iter_rewind_for_simple_replay_ai(
    struct monad_evsrc_any_iter *iter, uint64_t block_number,
    struct monad_event_descriptor *event, void const **payload)
{
    MONAD_DEFINE_EVSRC_OPS(source_ops, a)
    MONAD_DEFINE_EVSRC_ITER_OPS(iter_ops, a)
    return monad_exec_iter_rewind_for_simple_replay_generic(
        monad_evsrc_any_from_aci(iter),
        iter,
        block_number,
        event,
        payload,
        &source_ops,
        &iter_ops);
}

/*
 * monad_exec_get_most_recent_finalized
 */

inline bool monad_exec_get_most_recent_finalized(
    struct monad_event_ring const *event_ring, uint64_t *block_number)
{
    struct monad_event_ring_iter iter;
    struct monad_event_descriptor event;
    void const *payload;

    *block_number = 0;
    // Initialize an iterator to the latest position and copy out the event
    // there
    if (monad_event_ring_init_iterator(event_ring, &iter) != 0) {
        return false;
    }
    if (MONAD_UNLIKELY(
            monad_event_ring_iter_try_copy(&iter, &event) !=
            MONAD_EVENT_RING_SUCCESS)) {
        return false;
    }
    payload = monad_event_ring_payload_peek(event_ring, &event);

    // If this is not already pointing at a finalized event, scan backwards
    // to find the most recent BLOCK_FINALIZED event
    if (MONAD_LIKELY(event.event_type != MONAD_EXEC_BLOCK_FINALIZED)) {
        if (MONAD_UNLIKELY(!monad_exec_iter_consensus_prev_ri(
                &iter, MONAD_EXEC_BLOCK_FINALIZED, &event, &payload))) {
            return false;
        }
    }

    // Get the associated block number with this BLOCK_FINALIZED event
    if (MONAD_UNLIKELY(!monad_exec_get_block_number_r(
            event_ring, &event, payload, block_number))) {
        return false;
    }

    // We're almost done, but this block doesn't count if a call to
    // monad_exec_iter_rewind_for_simple_replay fails; the reason is that a
    // block number returned from here must be a "replayable since" marker;
    // if this fails then the event ring hasn't been populated enough yet,
    // or is overflowing; either way it should succeed eventually on a
    // subsequent call
    return monad_exec_iter_rewind_for_simple_replay_ri(
        &iter, *block_number, &event, &payload);
}
