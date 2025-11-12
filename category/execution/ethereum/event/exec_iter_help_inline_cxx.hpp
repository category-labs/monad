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

/**
 * @file
 *
 * This file contains C++ overloads sets that dispatch to the correct
 * exec iter helper function
 */

/*
 * monad_exec_get_block_number
 */

[[gnu::always_inline]] static inline bool monad_exec_get_block_number(
    monad_event_ring const *event_ring, monad_event_descriptor const *event,
    void const *payload, uint64_t *block_number)
{
    return monad_exec_get_block_number_r(
        event_ring, event, payload, block_number);
}

[[gnu::always_inline]] static inline bool monad_exec_get_block_number(
    monad_evcap_event_section const *event_section,
    monad_event_descriptor const *event, void const *payload,
    uint64_t *block_number)
{
    return monad_exec_get_block_number_c(
        event_section, event, payload, block_number);
}

[[gnu::always_inline]] static inline bool monad_exec_get_block_number(
    monad_evsrc_any const *any, monad_event_descriptor const *event,
    void const *payload, uint64_t *block_number)
{
    return monad_exec_get_block_number_a(any, event, payload, block_number);
}

/*
 * monad_exec_get_block_id
 */

[[gnu::always_inline]] static inline bool monad_exec_get_block_id(
    monad_event_ring const *event_ring, monad_event_descriptor const *event,
    void const *payload, monad_c_bytes32 *block_id)
{
    return monad_exec_get_block_id_r(event_ring, event, payload, block_id);
}

[[gnu::always_inline]] static inline bool monad_exec_get_block_id(
    monad_evcap_event_section const *event_section,
    monad_event_descriptor const *event, void const *payload,
    monad_c_bytes32 *block_id)
{
    return monad_exec_get_block_id_c(event_section, event, payload, block_id);
}

[[gnu::always_inline]] static inline bool monad_exec_get_block_id(
    monad_evsrc_any const *any, monad_event_descriptor const *event,
    void const *payload, monad_c_bytes32 *block_id)
{
    return monad_exec_get_block_id_a(any, event, payload, block_id);
}

/*
 * monad_exec_iter_consensus_prev
 */

[[gnu::always_inline]] static inline bool monad_exec_iter_consensus_prev(
    monad_event_ring_iter *iter, monad_exec_event_type event_type,
    monad_event_descriptor *event, void const **payload)
{
    return monad_exec_iter_consensus_prev_ri(iter, event_type, event, payload);
}

[[gnu::always_inline]] static inline bool monad_exec_iter_consensus_prev(
    monad_evcap_event_iter *iter, monad_exec_event_type event_type,
    monad_event_descriptor *event, void const **payload)
{
    return monad_exec_iter_consensus_prev_ci(iter, event_type, event, payload);
}

[[gnu::always_inline]] static inline bool monad_exec_iter_consensus_prev(
    monad_evsrc_any_iter *iter, monad_exec_event_type event_type,
    monad_event_descriptor *event, void const **payload)
{
    return monad_exec_iter_consensus_prev_ai(iter, event_type, event, payload);
}

/*
 * monad_exec_iter_block_number_prev
 */

[[gnu::always_inline]] static inline bool monad_exec_iter_block_number_prev(
    monad_event_ring_iter *iter, uint64_t block_number,
    monad_exec_event_type filter, monad_event_descriptor *event,
    void const **payload)
{
    return monad_exec_iter_block_number_prev_ri(
        iter, block_number, filter, event, payload);
}

[[gnu::always_inline]] static inline bool monad_exec_iter_block_number_prev(
    monad_evcap_event_iter *iter, uint64_t block_number,
    monad_exec_event_type filter, monad_event_descriptor *event,
    void const **payload)
{
    return monad_exec_iter_block_number_prev_ci(
        iter, block_number, filter, event, payload);
}

[[gnu::always_inline]] static inline bool monad_exec_iter_block_number_prev(
    monad_evsrc_any_iter *iter, uint64_t block_number,
    monad_exec_event_type filter, monad_event_descriptor *event,
    void const **payload)
{
    return monad_exec_iter_block_number_prev_ai(
        iter, block_number, filter, event, payload);
}

/*
 * monad_exec_iter_block_id_prev
 */

[[gnu::always_inline]] static inline bool monad_exec_iter_block_id_prev(
    monad_event_ring_iter *iter, monad_c_bytes32 const *block_id,
    monad_exec_event_type filter, monad_event_descriptor *event,
    void const **payload)
{
    return monad_exec_iter_block_id_prev_ri(
        iter, block_id, filter, event, payload);
}

[[gnu::always_inline]] static inline bool monad_exec_iter_block_id_prev(
    monad_evcap_event_iter *iter, monad_c_bytes32 const *block_id,
    monad_exec_event_type filter, monad_event_descriptor *event,
    void const **payload)
{
    return monad_exec_iter_block_id_prev_ci(
        iter, block_id, filter, event, payload);
}

[[gnu::always_inline]] static inline bool monad_exec_iter_block_id_prev(
    monad_evsrc_any_iter *iter, monad_c_bytes32 const *block_id,
    monad_exec_event_type filter, monad_event_descriptor *event,
    void const **payload)
{
    return monad_exec_iter_block_id_prev_ai(
        iter, block_id, filter, event, payload);
}

/*
 * monad_exec_iter_rewind_for_simple_replay
 */

[[gnu::always_inline]] static inline bool
monad_exec_iter_rewind_for_simple_replay(
    monad_event_ring_iter *iter, uint64_t block_number,
    monad_event_descriptor *event, void const **payload)
{
    return monad_exec_iter_rewind_for_simple_replay_ri(
        iter, block_number, event, payload);
}

[[gnu::always_inline]] static inline bool
monad_exec_iter_rewind_for_simple_replay(
    monad_evcap_event_iter *iter, uint64_t block_number,
    monad_event_descriptor *event, void const **payload)
{
    return monad_exec_iter_rewind_for_simple_replay_ci(
        iter, block_number, event, payload);
}

[[gnu::always_inline]] static inline bool
monad_exec_iter_rewind_for_simple_replay(
    monad_evsrc_any_iter *iter, uint64_t block_number,
    monad_event_descriptor *event, void const **payload)
{
    return monad_exec_iter_rewind_for_simple_replay_ai(
        iter, block_number, event, payload);
}
