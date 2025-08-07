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
 * This file defines iterator helpers for execution event rings. They are used
 * to efficiently rewind iterators for block-oriented replay, i.e., when the
 * user wants to replay whole blocks (and block consensus events) for old
 * events that are still resident in event ring memory.
 *
 * Note that in the documentation, `BLOCK_START` is considered a "consensus
 * event" because it represents the first state transition (to "proposed")
 */

#include <category/execution/ethereum/core/base_ctypes.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

enum monad_exec_event_type : uint16_t;

struct monad_event_descriptor;
struct monad_event_iterator;
struct monad_event_ring;
struct monad_exec_block_tag;

/// Extract the block number associated with an execution event; returns false
/// if the payload has expired or if there is no associated block number
static bool monad_exec_ring_get_block_number(
    struct monad_event_ring const *, struct monad_event_descriptor const *,
    uint64_t *block_number);

/// Return true if the execution event with the given descriptor relates to the
/// block with the given id
static bool monad_exec_ring_block_id_matches(
    struct monad_event_ring const *, struct monad_event_descriptor const *,
    monad_c_bytes32 const *);

/// Rewind the event ring iterator so that the next event produced by
/// `monad_event_iterator_try_next` will be the most recent consensus event
/// of the filter type, or `NONE` for any type; also copies out this previous
/// event's descriptor, i.e., behaves like `*--i`; if false is returned, the
/// iterator is not moved and the copied out event descriptor is not valid
static bool monad_exec_iter_consensus_prev(
    struct monad_event_iterator *, enum monad_exec_event_type filter,
    struct monad_event_descriptor *);

/// Rewind the event ring iterator, as if by repeatedly calling
/// `monad_exec_iter_consensus_prev`, stopping only when the block number
/// associated with the event matches the specified block number
static bool monad_exec_iter_block_number_prev(
    struct monad_event_iterator *, struct monad_event_ring const *,
    uint64_t block_number, enum monad_exec_event_type filter,
    struct monad_event_descriptor *);

/// Rewind the event ring iterator, as if by repeatedly calling
/// `monad_exec_iter_consensus_prev`, stopping only when the block ID
/// associated with the event matches the specified block ID; BLOCK_VERIFIED
/// is not an allowed filter type, because block IDs are not recorded for
/// these events
static bool monad_exec_iter_block_id_prev(
    struct monad_event_iterator *, struct monad_event_ring const *,
    monad_c_bytes32 const *, enum monad_exec_event_type filter,
    struct monad_event_descriptor *);

/// Rewind the event ring iterator, following the "simple replay strategy",
/// which is to replay all events that you may not have seen, if the last
/// finalized block you definitely saw is `block_number`
static bool monad_exec_iter_rewind_for_simple_replay(
    struct monad_event_iterator *, struct monad_event_ring const *,
    uint64_t block_number, struct monad_event_descriptor *);

#ifdef __cplusplus
} // extern "C"
#endif

#define MONAD_EXEC_ITER_HELP_INTERNAL
#include "exec_iter_help_inline.h"
#undef MONAD_EXEC_ITER_HELP_INTERNAL
