#pragma once

/**
 * @file
 *
 * This file defines iterator helpers for execution event rings. They are used
 * to efficiently rewind iterators for block-oriented replay, i.e., when the
 * user wants to replay whole blocks (and block consensus events) for old
 * events that are still resident in event ring memory.
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

/// Return true if the execution event with the given descriptor has an
/// unexpired payload and is associated with the given block id
static bool monad_exec_ring_block_id_matches(
    struct monad_event_ring const *, struct monad_event_descriptor const *,
    monad_c_bytes32 const *);

/// Rewinds the event ring iterator so that the next event produced by
/// `monad_event_iterator_try_next` will be the most recent consensus event
/// of the given type (i.e., `BLOCK_START`, `BLOCK_QC`, `BLOCK_FINALIZED`, or
/// `BLOCK_VERIFIED` event); also copies out this previous event, i.e., this
/// behaves like `*--i`; returns false if the iterator cannot be moved back
static bool monad_exec_iter_consensus_prev(
    struct monad_event_iterator *, enum monad_exec_event_type filter,
    struct monad_event_descriptor *);

/// Rewind to the previous consensus event of the specified type, for the
/// specified block number, and copy out its event descriptor; the iterator is
/// set so that the next call to `monad_event_iterator_try_next` will be the
/// event following the requested consensus event; if false is returned, the
/// iterator is not moved and the copied out event descriptor is not valid
static bool monad_exec_iter_block_number_prev(
    struct monad_event_iterator *, struct monad_event_ring const *,
    uint64_t block_number, enum monad_exec_event_type filter,
    struct monad_event_descriptor *);

/// Given a block tag, seek to the consensus event with that tag and the given
/// event type; `monad_exec_event_type` can be `BLOCK_START`, `BLOCK_QC`,
/// or `BLOCK_FINALIZED` to look only for events of this type, or `NONE` to
/// return events of any type
static bool monad_exec_iter_block_id_prev(
    struct monad_event_iterator *, struct monad_event_ring const *,
    monad_c_bytes32 const *, enum monad_exec_event_type filter,
    struct monad_event_descriptor *);

#ifdef __cplusplus
} // extern "C"
#endif

#define MONAD_EXEC_ITER_HELP_INTERNAL
#include "exec_iter_help_inline.h"
#undef MONAD_EXEC_ITER_HELP_INTERNAL
