#ifndef MONAD_EXEC_ITER_HELP_INTERNAL
    #error This file should only be included directly by exec_event_iter_help.h
#endif

#include <assert.h>
#include <stdint.h>
#include <string.h>

#include <category/core/event/event_iterator.h>
#include <category/core/event/event_ring.h>
#include <category/execution/ethereum/core/base_ctypes.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

// For functions like monad_exec_ring_get_block_number, we expect the user to
// pass a descriptor containing a consensus event (or BLOCK_START); if this is
// not the case, we need to seek to the nearest BLOCK_START and copy that
// event into an API-provided buffer, then reseat the event pointer to refer
// to that event buffer instead
static inline bool _monad_exec_ring_ensure_block(
    struct monad_event_ring const *event_ring,
    struct monad_event_descriptor const **event_p,
    struct monad_event_descriptor *buf)
{
    if (__builtin_expect(
            (*event_p)->user[MONAD_FLOW_BLOCK_SEQNO] != 0 &&
                (*event_p)->event_type != MONAD_EXEC_BLOCK_START,
            0)) {
        if (__builtin_expect(
                !monad_event_ring_try_copy(
                    event_ring, (*event_p)->user[MONAD_FLOW_BLOCK_SEQNO], buf),
                0)) {
            return false;
        }
        *event_p = buf;
    }
    return true;
}

inline bool monad_exec_ring_get_block_number(
    struct monad_event_ring const *event_ring,
    struct monad_event_descriptor const *event, uint64_t *block_number)
{
    struct monad_event_descriptor buf;
    void const *payload;

    if (__builtin_expect(
            !_monad_exec_ring_ensure_block(event_ring, &event, &buf), 0)) {
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

    if (__builtin_expect(
            !_monad_exec_ring_ensure_block(event_ring, &event, &buf), 0)) {
        return false;
    }

    payload = monad_event_ring_payload_peek(event_ring, event);

    switch (event->event_type) {
    case MONAD_EXEC_BLOCK_START:
        tag_matches = memcmp(
                          block_id,
                          ((struct monad_exec_block_start const *)payload)
                              ->block_tag.id.bytes,
                          sizeof *block_id) == 0;
        break;

    case MONAD_EXEC_BLOCK_QC:
        tag_matches = memcmp(
                          block_id,
                          ((struct monad_exec_block_qc const *)payload)
                              ->block_tag.id.bytes,
                          sizeof *block_id) == 0;
        break;

    case MONAD_EXEC_BLOCK_FINALIZED:
        tag_matches =
            memcmp(
                block_id,
                ((struct monad_exec_block_tag const *)payload)->id.bytes,
                sizeof &block_id) == 0;
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
    enum monad_exec_event_type event_type;
    uint64_t iter_save = iter->read_last_seqno;

    if (event == nullptr) {
        event = &buf;
    }

    if (iter->read_last_seqno > 0 &&
        monad_event_iterator_try_copy(iter, event) == MONAD_EVENT_SUCCESS &&
        event->user[MONAD_FLOW_BLOCK_SEQNO] != 0 &&
        event->event_type != MONAD_EXEC_BLOCK_START) {
        iter->read_last_seqno = event->user[MONAD_FLOW_BLOCK_SEQNO] - 1;
        // A special case to rewind to the start of a block boundary, if we
        // didn't start at one
        if (filter == MONAD_EXEC_NONE || filter == MONAD_EXEC_BLOCK_START) {
            return monad_event_iterator_try_copy(iter, event) ==
                   MONAD_EVENT_SUCCESS;
        }
    }

    while (__builtin_expect(
        iter->read_last_seqno > 0 &&
            monad_event_iterator_try_copy(iter, event) == MONAD_EVENT_SUCCESS,
        0)) {
        event_type = (enum monad_exec_event_type)event->event_type;
        if (event->user[MONAD_FLOW_BLOCK_SEQNO] != 0 &&
            event->event_type != MONAD_EXEC_BLOCK_START) {
            iter->read_last_seqno = event->user[MONAD_FLOW_BLOCK_SEQNO] - 1;
            continue;
        }
        --iter->read_last_seqno;
        if (filter == MONAD_EXEC_NONE || filter == event_type) {
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
        return false;
    }

    if (event == nullptr) {
        event = &buf;
    }

    while (__builtin_expect(
        monad_exec_iter_consensus_prev(iter, filter, event), 1)) {
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
        return false;
    }

    if (event == nullptr) {
        event = &buf;
    }

    while (__builtin_expect(
        monad_exec_iter_consensus_prev(iter, filter, event), 1)) {
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
