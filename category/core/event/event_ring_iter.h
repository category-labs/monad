// Copyright (C) 2025-26 Category Labs, Inc.
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
 * Defines the event ring iterator object and its API; iterators are used for
 * reading events
 */

#include <stddef.h>
#include <stdint.h>

#include <category/core/event/event_def.h>
#include <category/core/event/event_ring.h>
#include <category/core/likely.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_event_ring_control;
struct monad_event_ring_iter;

/// Copy the next event descriptor and advance the iterator, if the next event
/// is available, similar to `*i++`; returns MONAD_EVENT_RING_SUCCESS upon
/// success, otherwise a code indicating why the iterator could not be advanced
static monad_event_ring_result_t monad_event_ring_iter_try_next(
    struct monad_event_ring_iter *, struct monad_event_descriptor *);

/// Move the iterator back to previous event descriptor and copy it out, if the
/// previous event is still available, similar to `*--i`; return behavior is
/// the same as monad_event_ring_iter_try_next
static monad_event_ring_result_t monad_event_ring_iter_try_prev(
    struct monad_event_ring_iter *, struct monad_event_descriptor *);

/// Copy the event descriptor at the current iteration point, without advancing
/// the iterator; returns MONAD_EVENT_RING_SUCCESS upon success, otherwise a
/// code indicating why the descriptor at the iteration point was not ready
static monad_event_ring_result_t monad_event_ring_iter_try_copy(
    struct monad_event_ring_iter const *, struct monad_event_descriptor *);

/// Unchecked advance of the iterator by a signed distance; the typical
/// iteration pattern is to use monad_event_ring_iter_try_next, which performs
/// `*i++` atomically if and only if an event is ready, but the caller can also
/// use `monad_event_ring_iter_try_copy`/ and `monad_event_ring_iter_advance`
/// (which is unchecked) in certain situations
static uint64_t
monad_event_ring_iter_advance(struct monad_event_ring_iter *, int64_t distance);

/// Set the iterator so that the next call to `monad_event_ring_iter_try_next`
/// or `monad_event_ring_iter_try_copy` will read the event descriptor with the
/// specified sequence number; this performs no checking
static void
monad_event_ring_iter_set_seqno(struct monad_event_ring_iter *, uint64_t seqno);

/// Reset the iterator to point to the latest event produced; used for gap
/// recovery
static uint64_t monad_event_ring_iter_reset(struct monad_event_ring_iter *);

// clang-format off

/// Holds the state of a single event iterator
struct monad_event_ring_iter
{
    struct monad_event_ring const *event_ring;
    uint64_t cur_seqno;
};

// clang-format on

/*
 * Inline implementation
 */

inline monad_event_ring_result_t monad_event_ring_iter_try_next(
    struct monad_event_ring_iter *const iter,
    struct monad_event_descriptor *const event)
{
    monad_event_ring_result_t const r =
        monad_event_ring_iter_try_copy(iter, event);
    if (MONAD_LIKELY(r == MONAD_EVENT_RING_SUCCESS)) {
        ++iter->cur_seqno;
    }
    return r;
}

inline monad_event_ring_result_t monad_event_ring_iter_try_prev(
    struct monad_event_ring_iter *const iter,
    struct monad_event_descriptor *const event)
{
    if (MONAD_UNLIKELY(iter->cur_seqno == 1)) {
        return MONAD_EVENT_RING_NOT_READY;
    }
    --iter->cur_seqno;
    monad_event_ring_result_t const r =
        monad_event_ring_iter_try_copy(iter, event);
    if (MONAD_UNLIKELY(r != MONAD_EVENT_RING_SUCCESS)) {
        ++iter->cur_seqno;
    }
    return r;
}

inline monad_event_ring_result_t monad_event_ring_iter_try_copy(
    struct monad_event_ring_iter const *const iter,
    struct monad_event_descriptor *const event)
{
    return monad_event_ring_try_copy(iter->event_ring, iter->cur_seqno, event);
}

inline uint64_t monad_event_ring_iter_advance(
    struct monad_event_ring_iter *const iter, int64_t const distance)
{
    int64_t const new_position = (int64_t)iter->cur_seqno + distance;
    if (MONAD_UNLIKELY(new_position < 1)) {
        iter->cur_seqno = 1;
    }
    else {
        iter->cur_seqno = (uint64_t)new_position;
    }
    return iter->cur_seqno;
}

inline void monad_event_ring_iter_set_seqno(
    struct monad_event_ring_iter *const iter, uint64_t const seqno)
{
    iter->cur_seqno = seqno;
}

inline uint64_t
monad_event_ring_iter_reset(struct monad_event_ring_iter *const iter)
{
    uint64_t const last_available_seqno =
        monad_event_ring_get_last_written_seqno(
            iter->event_ring, /*sync_wait*/ true);
    return iter->cur_seqno =
               last_available_seqno > 0 ? last_available_seqno : 1;
}

#ifdef __cplusplus
} // extern "C"
#endif
