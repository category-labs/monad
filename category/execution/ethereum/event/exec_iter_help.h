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

#include <stdint.h>

#include <category/core/event/event_source.h>
#include <category/execution/ethereum/core/base_ctypes.h>

#ifdef __cplusplus
extern "C"
{
#endif

enum monad_exec_event_type : uint16_t;

struct monad_event_descriptor;
struct monad_event_ring;
struct monad_evsrc;
struct monad_evsrc_iterator;
struct monad_exec_block_tag;

/*
 * bool monad_exec_get_block_number(
 *     GENERIC_SOURCE, struct monad_event_descriptor const *,
 *     void const *payload, uint64_t *block_number)
 *
 * Extract the block number associated with an execution event; returns false
 * if the payload has expired or if there is no associated block number
 */

MONAD_SDK_EVSRC_DECL(
    bool, monad_exec_get_block_number, struct monad_event_descriptor const *,
    void const *payload, uint64_t *block_number)

/*
 * bool monad_exec_get_block_id(
 *     GENERIC_SOURCE, struct monad_event_descriptor const *,
 *     void const *payload, monad_c_bytes32 *)
 *
 * Extract the block id associated with an execution event; returns false
 * if the payload has expired or if there is no associated block id
 */

MONAD_SDK_EVSRC_DECL(
    bool, monad_exec_get_block_id, struct monad_event_descriptor const *,
    void const *payload, monad_c_bytes32 *)

/*
 * bool monad_exec_iter_consensus_prev(
 *     GENERIC_ITER, enum monad_exec_event_type filter,
 *     struct monad_event_descriptor *, void const **payload)
 *
 * Rewind the event ring iterator so that the next event produced by
 * `monad_evsrc_iter_try_next` will be the most recent consensus event of the
 * filter type, or `NONE` for any type; also copies out this previous event's
 * event's descriptor, i.e., behaves like `*--i`; if false is returned, the
 * iterator is not moved and the copied out event descriptor is not valid
 */

MONAD_SDK_EVSRC_ITER_DECL(
    bool, monad_exec_iter_consensus_prev, enum monad_exec_event_type,
    struct monad_event_descriptor *, void const **)

/*
 * bool monad_exec_iter_block_number_prev(
 *      GENERIC_ITER, uint64_t block_number, enum monad_exec_event_type filter,
 *      struct monad_event_descriptor *, void const **payload);
 *
 * Rewind the event ring iterator, as if by repeatedly calling
 * `monad_exec_iter_consensus_prev`, stopping only when the block number
 * associated with the event matches the specified block number
 */

MONAD_SDK_EVSRC_ITER_DECL(
    bool, monad_exec_iter_block_number_prev, uint64_t,
    enum monad_exec_event_type, struct monad_event_descriptor *, void const **)

/*
 * bool monad_exec_iter_block_id_prev(
 *     GENERIC_ITER, monad_c_bytes32 const *, enum monad_exec_event_type filter,
 *     struct monad_event_descriptor *, void const **payload);
 *
 * Rewind the event ring iterator, as if by repeatedly calling
 * `monad_exec_iter_consensus_prev`, stopping only when the block ID
 * associated with the event matches the specified block ID; BLOCK_VERIFIED
 * is not an allowed filter type, because block IDs are not recorded for
 * these events
 */

MONAD_SDK_EVSRC_ITER_DECL(
    bool, monad_exec_iter_block_id_prev, monad_c_bytes32 const *,
    enum monad_exec_event_type, struct monad_event_descriptor *, void const **)

/*
 * bool monad_exec_iter_rewind_for_simple_replay(
 *     GENERIC_ITER, uint64_t block_number, struct monad_event_descriptor *,
 *     void const **payload);
 *
 * Rewind the event ring iterator, following the "simple replay strategy",
 * which is to replay all events that you may not have seen, if the last
 * finalized block you definitely saw is `block_number`. This will replay
 * all events that occur _after_ the original proposal of the finalized
 * block, i.e., all events after the `BLOCK_END` of the block that was
 * ultimately finalized. In particular, you may see the BLOCK_QC and
 * BLOCK_FINALIZED event of the finalized block a second time.
 */

MONAD_SDK_EVSRC_ITER_DECL(
    bool, monad_exec_iter_rewind_for_simple_replay, uint64_t,
    struct monad_event_descriptor *, void const **)

/*
 * Non-generic functions - these make sense only for certain kind of events
 * sources
 */

/// Return the number of most recently finalized block, for which the full
/// proposal's events are also still available. This is used as part of the
/// simple replay strategy, when a large number of blocks are missing.
///
/// The typical approach involves constructing the range
/// (last_known_finalized, most_recent_finalized] which must be replayed from
/// event captures, prior to switching back over to the live ring to obtain
/// everything _after_ `most_recent_finalized`, which is done via the function
/// monad_exec_iter_rewind_for_simple_replay
static bool monad_exec_get_most_recent_finalized(
    struct monad_event_ring const *, uint64_t *block_number);

#ifdef __cplusplus
} // extern "C"
#endif

#define MONAD_EXEC_ITER_HELP_INTERNAL
#include "exec_iter_help_inline.h"

#ifdef __cplusplus
    #include "exec_iter_help_inline_cxx.hpp"
#else
    #include "exec_iter_help_inline_c_generic.h"
#endif

#undef MONAD_EXEC_ITER_HELP_INTERNAL
