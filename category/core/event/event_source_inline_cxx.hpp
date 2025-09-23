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

#ifndef MONAD_EVENT_SOURCE_INTERNAL
    #error This file should only be included directly by event_source.h
#endif

/**
 * @file
 *
 * This file contains C++ overloads sets that dispatch to the correct
 * event source function
 */

/*
 * monad_evsrc_check_payload
 */

[[gnu::always_inline]] static inline bool monad_evsrc_check_payload(
    monad_event_ring const *r, monad_event_descriptor const *event)
{
    return monad_evsrc_check_payload_r(r, event);
}

[[gnu::always_inline]] static inline bool monad_evsrc_check_payload(
    monad_evcap_event_section const *c, monad_event_descriptor const *event)
{
    return monad_evsrc_check_payload_c(c, event);
}

[[gnu::always_inline]] static inline bool monad_evsrc_check_payload(
    monad_evsrc_any const *a, monad_event_descriptor const *event)
{
    return monad_evsrc_check_payload_a(a, event);
}

/*
 * monad_evsrc_copy_seqno
 */

[[gnu::always_inline]] static inline monad_evsrc_result_t
monad_evsrc_copy_seqno(
    monad_event_ring const *r, uint64_t seqno, monad_event_descriptor *event,
    void const **payload)
{
    return monad_evsrc_copy_seqno_r(r, seqno, event, payload);
}

[[gnu::always_inline]] static inline monad_evsrc_result_t
monad_evsrc_copy_seqno(
    monad_evcap_event_section const *c, uint64_t seqno,
    monad_event_descriptor *event, void const **payload)
{
    return monad_evsrc_copy_seqno_c(c, seqno, event, payload);
}

[[gnu::always_inline]] static inline monad_evsrc_result_t
monad_evsrc_copy_seqno(
    monad_evsrc_any const *a, uint64_t seqno, monad_event_descriptor *event,
    void const **payload)
{
    return monad_evsrc_copy_seqno_a(a, seqno, event, payload);
}

/*
 * monad_evsrc_close
 */

[[gnu::always_inline]] static inline void monad_evsrc_close(monad_event_ring *r)
{
    return monad_evsrc_close_r(r);
}

[[gnu::always_inline]] static inline void
monad_evsrc_close(monad_evcap_event_section *c)
{
    return monad_evsrc_close_c(c);
}

[[gnu::always_inline]] static inline void monad_evsrc_close(monad_evsrc_any *a)
{
    return monad_evsrc_close_a(a);
}

/*
 * monad_evsrc_any_from
 */

[[gnu::always_inline]]
static inline monad_evsrc_any const *
monad_evsrc_any_from(monad_event_ring const *r)
{
    return monad_evsrc_any_from_r(r);
}

[[gnu::always_inline]]
static inline monad_evsrc_any const *
monad_evsrc_any_from(monad_evcap_event_section const *c)
{
    return monad_evsrc_any_from_c(c);
}

[[gnu::always_inline]]
static inline monad_evsrc_any const *
monad_evsrc_any_from(monad_event_ring_iter const *rci)
{
    return monad_evsrc_any_from_rci(rci);
}

[[gnu::always_inline]]
static inline monad_evsrc_any const *
monad_evsrc_any_from(monad_evcap_event_iter const *cci)
{
    return monad_evsrc_any_from_cci(cci);
}

[[gnu::always_inline]]
static inline monad_evsrc_any const *
monad_evsrc_any_from(monad_evsrc_any_iter const *aci)
{
    return monad_evsrc_any_from_aci(aci);
}

/*
 * monad_evsrc_any_iter_from
 */

[[gnu::always_inline]] static inline monad_evsrc_any_iter *
monad_evsrc_any_iter_from(monad_event_ring_iter *i)
{
    return monad_evsrc_any_iter_from_ri(i);
}

[[gnu::always_inline]] static inline monad_evsrc_any_iter *
monad_evsrc_any_iter_from(monad_evcap_event_iter *i)
{
    return monad_evsrc_any_iter_from_ci(i);
}

[[gnu::always_inline]] static inline monad_evsrc_any_iter *
monad_evsrc_any_iter_from(monad_evsrc_any_iter *i)
{
    return monad_evsrc_any_iter_from_ai(i);
}

/*
 * monad_evsrc_iter_try_next
 */

[[gnu::always_inline]] static inline monad_evsrc_result_t
monad_evsrc_iter_try_next(
    monad_event_ring_iter *i, monad_event_descriptor *event,
    void const **payload)
{
    return monad_evsrc_iter_try_next_ri(i, event, payload);
}

[[gnu::always_inline]] static inline monad_evsrc_result_t
monad_evsrc_iter_try_next(
    monad_evcap_event_iter *i, monad_event_descriptor *event,
    void const **payload)
{
    return monad_evsrc_iter_try_next_ci(i, event, payload);
}

[[gnu::always_inline]] static inline monad_evsrc_result_t
monad_evsrc_iter_try_next(
    monad_evsrc_any_iter *i, monad_event_descriptor *event,
    void const **payload)
{
    return monad_evsrc_iter_try_next_ai(i, event, payload);
}

/*
 * monad_evsrc_iter_try_prev
 */

[[gnu::always_inline]] static inline monad_evsrc_result_t
monad_evsrc_iter_try_prev(
    monad_event_ring_iter *i, monad_event_descriptor *event,
    void const **payload)
{
    return monad_evsrc_iter_try_prev_ri(i, event, payload);
}

[[gnu::always_inline]] static inline monad_evsrc_result_t
monad_evsrc_iter_try_prev(
    monad_evcap_event_iter *i, monad_event_descriptor *event,
    void const **payload)
{
    return monad_evsrc_iter_try_prev_ci(i, event, payload);
}

[[gnu::always_inline]] static inline monad_evsrc_result_t
monad_evsrc_iter_try_prev(
    monad_evsrc_any_iter *i, monad_event_descriptor *event,
    void const **payload)
{
    return monad_evsrc_iter_try_prev_ai(i, event, payload);
}

/*
 * monad_evsrc_iter_set_seqno
 */

[[gnu::always_inline]] static inline monad_evsrc_result_t
monad_evsrc_iter_set_seqno(monad_event_ring_iter *i, uint64_t seqno)
{
    return monad_evsrc_iter_set_seqno_ri(i, seqno);
}

[[gnu::always_inline]] static inline monad_evsrc_result_t
monad_evsrc_iter_set_seqno(monad_evcap_event_iter *i, uint64_t seqno)
{
    return monad_evsrc_iter_set_seqno_ci(i, seqno);
}

[[gnu::always_inline]] static inline monad_evsrc_result_t
monad_evsrc_iter_set_seqno(monad_evsrc_any_iter *i, uint64_t seqno)
{
    return monad_evsrc_iter_set_seqno_ai(i, seqno);
}

/*
 * monad_evsrc_iter_seek
 */

[[gnu::always_inline]] static inline void
monad_evsrc_iter_seek(monad_event_ring_iter *i, uint64_t position)
{
    return monad_evsrc_iter_seek_ri(i, position);
}

[[gnu::always_inline]] static inline void
monad_evsrc_iter_seek(monad_evcap_event_iter *i, uint64_t position)
{
    return monad_evsrc_iter_seek_ci(i, position);
}

[[gnu::always_inline]] static inline void
monad_evsrc_iter_seek(monad_evsrc_any_iter *i, uint64_t position)
{
    return monad_evsrc_iter_seek_ai(i, position);
}

/*
 * monad_evsrc_iter_reset
 */

[[gnu::always_inline]] static inline uint64_t
monad_evsrc_iter_reset(monad_event_ring_iter *i)
{
    return monad_evsrc_iter_reset_ri(i);
}

[[gnu::always_inline]] static inline uint64_t
monad_evsrc_iter_reset(monad_evcap_event_iter *i)
{
    return monad_evsrc_iter_reset_ci(i);
}

[[gnu::always_inline]] static inline uint64_t
monad_evsrc_iter_reset(monad_evsrc_any_iter *i)
{
    return monad_evsrc_iter_reset_ai(i);
}

/*
 * monad_evsrc_const_any_iter_from
 */

[[gnu::always_inline]] static inline monad_evsrc_any_iter const *
monad_evsrc_const_any_iter_from(monad_event_ring_iter *i)
{
    return monad_evsrc_const_any_iter_from_ri(i);
}

[[gnu::always_inline]] static inline monad_evsrc_any_iter const *
monad_evsrc_const_any_iter_from(monad_evcap_event_iter *i)
{
    return monad_evsrc_const_any_iter_from_ci(i);
}

[[gnu::always_inline]] static inline monad_evsrc_any_iter const *
monad_evsrc_const_any_iter_from(monad_evsrc_any_iter *i)
{
    return monad_evsrc_const_any_iter_from_ai(i);
}

/*
 * monad_evsrc_iter_try_copy
 */

[[gnu::always_inline]] static inline monad_evsrc_result_t
monad_evsrc_iter_try_copy(
    monad_event_ring_iter const *i, monad_event_descriptor *event,
    void const **payload)
{
    return monad_evsrc_iter_try_copy_rci(i, event, payload);
}

[[gnu::always_inline]] static inline monad_evsrc_result_t
monad_evsrc_iter_try_copy(
    monad_evcap_event_iter const *i, monad_event_descriptor *event,
    void const **payload)
{
    return monad_evsrc_iter_try_copy_cci(i, event, payload);
}

[[gnu::always_inline]] static inline monad_evsrc_result_t
monad_evsrc_iter_try_copy(
    monad_evsrc_any_iter const *i, monad_event_descriptor *event,
    void const **payload)
{
    return monad_evsrc_iter_try_copy_aci(i, event, payload);
}

/*
 * monad_evsrc_iter_tell
 */

[[gnu::always_inline]] static inline uint64_t
monad_evsrc_iter_tell(monad_event_ring_iter const *i)
{
    return monad_evsrc_iter_tell_rci(i);
}

[[gnu::always_inline]] static inline uint64_t
monad_evsrc_iter_tell(monad_evcap_event_iter const *i)
{
    return monad_evsrc_iter_tell_cci(i);
}

[[gnu::always_inline]] static inline uint64_t
monad_evsrc_iter_tell(monad_evsrc_any_iter const *i)
{
    return monad_evsrc_iter_tell_aci(i);
}
