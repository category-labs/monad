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

/*
 * The basic idea is explained in the event_source.h file-level comment.
 *
 * The "evsrc" common API unifies the event ring and evcap reader APIs, which
 * are slightly different given the different ways events are organized in
 * memory. The differences are:
 *
 *   - The evcap API must read the event descriptor and payload together at
 *     the same time. It reads them both "zero copy" since the events data
 *     is mmap'ed in memory and never expires
 *
 *   - The event ring API reads descriptors and payloads separately; descriptors
 *     are copied (after performing some atomic operations to check for gaps)
 *     while payload access is "zero-copy"; payloads can also expire
 *
 * In the unified interface, descriptors are copied in both, and event payload
 * pointers are always returned together with descriptors. This table shows what
 * the implementation functions generally do:
 *
 * Source type | suffix | how its native API is adjusted to the common one
 * ----------- | ------ | ----------------------------------------------
 *  event ring |   _r   | payload peek at the same time as descriptor is copied
 *  evcap file |   _c   | event descriptor is explicitly copied
 *  evsrc any  |   _a   | tagged pointer indicates runtime type; calls _r or _c
 *
 * To make it work naturally across all three languages requires a lot of tiny
 * wrapper functions which do very little. Many clever programming techniques
 * were explored to reduce the verbosity, but all destroyed the inlinability,
 * which in the Rust case must be done at link time via LTO. Other clever
 * approaches using macros or templates are able to reduce the source code
 * footprint somewhat, but any such approach is likely to be hard to understand.
 * As a result, the full event source implementation is about 1000 lines of
 * code, but all of the code is trivial "boilerplate" -- the kind that could
 * be generated.
 */

#include <stddef.h>
#include <stdint.h>

#include <category/core/event/evcap_reader.h>
#include <category/core/event/event_def.h>
#include <category/core/event/event_ring.h>
#include <category/core/event/event_ring_iter.h>
#include <category/core/likely.h>

#ifdef __cplusplus
extern "C"
{
#endif

union monad_evsrc_any_decoded
{
    struct monad_event_ring const *event_ring;
    struct monad_evcap_event_section const *event_section;
};

union monad_evsrc_any_iter_decoded
{
    struct monad_event_ring_iter *ring_iter;
    struct monad_evcap_event_iter *evcap_iter;
};

union monad_evsrc_const_any_iter_decoded
{
    struct monad_event_ring_iter const *ring_iter;
    struct monad_evcap_event_iter const *evcap_iter;
};

static inline monad_evsrc_type_t monad_evsrc_any_decode(
    struct monad_evsrc_any const *any, union monad_evsrc_any_decoded *u)
{
    uintptr_t const address = (uintptr_t)any;
    if (address & 0b1) {
        u->event_section =
            (struct monad_evcap_event_section const *)(address &
                                                       ~(uintptr_t)0b1);
        return MONAD_EVSRC_EVCAP_SECTION;
    }
    else {
        u->event_ring = (struct monad_event_ring const *)address;
        return MONAD_EVSRC_EVENT_RING;
    }
}

static inline monad_evsrc_type_t monad_evsrc_const_any_iter_decode(
    struct monad_evsrc_any_iter const *iter,
    union monad_evsrc_const_any_iter_decoded *u)
{
    uintptr_t const address = (uintptr_t)iter;
    if (address & 0b1) {
        u->evcap_iter =
            (struct monad_evcap_event_iter const *)(address & ~(uintptr_t)0b1);
        return MONAD_EVSRC_EVCAP_SECTION;
    }
    else {
        u->ring_iter = (struct monad_event_ring_iter const *)address;
        return MONAD_EVSRC_EVENT_RING;
    }
}

static inline monad_evsrc_type_t monad_evsrc_any_iter_decode(
    struct monad_evsrc_any_iter *iter, union monad_evsrc_any_iter_decoded *u)
{
    return monad_evsrc_const_any_iter_decode(
        iter, (union monad_evsrc_const_any_iter_decoded *)u);
}

inline monad_evsrc_type_t
monad_evsrc_any_get_type(struct monad_evsrc_any const *any)
{
    union monad_evsrc_any_decoded u;
    return monad_evsrc_any_decode(any, &u);
}

inline monad_evsrc_type_t
monad_evsrc_any_iter_get_type(struct monad_evsrc_any_iter const *i)
{
    union monad_evsrc_const_any_iter_decoded u;
    return monad_evsrc_const_any_iter_decode(i, &u);
}

/*
 * monad_evsrc_check_payload
 */

inline bool monad_evsrc_check_payload_r(
    struct monad_event_ring const *event_ring,
    struct monad_event_descriptor const *event)
{
    return monad_event_ring_payload_check(event_ring, event);
}

inline bool monad_evsrc_check_payload_c(
    struct monad_evcap_event_section const *,
    struct monad_event_descriptor const *)
{
    return true;
}

inline bool monad_evsrc_check_payload_a(
    struct monad_evsrc_any const *any,
    struct monad_event_descriptor const *event)
{
    union monad_evsrc_any_decoded u;
    switch (monad_evsrc_any_decode(any, &u)) {
    case MONAD_EVSRC_EVENT_RING:
        return monad_evsrc_check_payload_r(u.event_ring, event);
    case MONAD_EVSRC_EVCAP_SECTION:
        return monad_evsrc_check_payload_c(u.event_section, event);
    default:
        __builtin_unreachable();
    }
}

/*
 * monad_evsrc_copy_seqno
 */

inline monad_evsrc_result_t monad_evsrc_copy_seqno_r(
    struct monad_event_ring const *event_ring, uint64_t seqno,
    struct monad_event_descriptor *event, void const **payload)
{
    monad_event_ring_result_t const r =
        monad_event_ring_try_copy(event_ring, seqno, event);
    if (payload != nullptr) {
        *payload = r == MONAD_EVENT_RING_SUCCESS &&
                           monad_event_ring_payload_check(event_ring, event)
                       ? monad_event_ring_payload_peek(event_ring, event)
                       : nullptr;
    }
    return (monad_evsrc_result_t)r;
}

inline monad_evsrc_result_t monad_evsrc_copy_seqno_c(
    struct monad_evcap_event_section const *event_section, uint64_t seqno,
    struct monad_event_descriptor *event, void const **payload)
{
    struct monad_event_descriptor const *evcap_event = nullptr;
    monad_evcap_read_result_t const r = monad_evcap_event_section_copy_seqno(
        event_section, seqno, &evcap_event, payload);
    if (MONAD_LIKELY(r == MONAD_EVCAP_READ_SUCCESS)) {
        *event = *evcap_event;
    }
    return (monad_evsrc_result_t)r;
}

inline monad_evsrc_result_t monad_evsrc_copy_seqno_a(
    struct monad_evsrc_any const *any, uint64_t seqno,
    struct monad_event_descriptor *event, void const **payload)
{
    union monad_evsrc_any_decoded u;
    switch (monad_evsrc_any_decode(any, &u)) {
    case MONAD_EVSRC_EVENT_RING:
        return monad_evsrc_copy_seqno_r(u.event_ring, seqno, event, payload);
    case MONAD_EVSRC_EVCAP_SECTION:
        return monad_evsrc_copy_seqno_c(u.event_section, seqno, event, payload);
    default:
        __builtin_unreachable();
    }
}

/*
 * monad_evsrc_close
 */

inline void monad_evsrc_close_r(struct monad_event_ring *) {}

inline void monad_evsrc_close_c(struct monad_evcap_event_section *event_section)
{
    monad_evcap_event_section_close(event_section);
}

inline void monad_evsrc_close_a(struct monad_evsrc_any *any)
{
    union monad_evsrc_any_decoded u;
    switch (monad_evsrc_any_decode(any, &u)) {
    case MONAD_EVSRC_EVENT_RING:
        return monad_evsrc_close_r((struct monad_event_ring *)u.event_ring);
    case MONAD_EVSRC_EVCAP_SECTION:
        return monad_evsrc_close_c(
            (struct monad_evcap_event_section *)u.event_section);
    default:
        __builtin_unreachable();
    }
}

/*
 * monad_evsrc_any_from
 */

inline struct monad_evsrc_any const *
monad_evsrc_any_from_r(struct monad_event_ring const *event_ring)
{
    return (struct monad_evsrc_any const *)event_ring;
}

inline struct monad_evsrc_any const *
monad_evsrc_any_from_c(struct monad_evcap_event_section const *event_section)
{
    uintptr_t const address = (uintptr_t)event_section | 0b1;
    return (struct monad_evsrc_any const *)address;
}

inline struct monad_evsrc_any const *
monad_evsrc_any_from_a(struct monad_evsrc_any const *any)
{
    return any;
}

inline struct monad_evsrc_any const *
monad_evsrc_any_from_rci(struct monad_event_ring_iter const *i)
{
    return monad_evsrc_any_from_r(i->event_ring);
}

inline struct monad_evsrc_any const *
monad_evsrc_any_from_cci(struct monad_evcap_event_iter const *i)
{
    return monad_evsrc_any_from_c(i->event_section);
}

inline struct monad_evsrc_any const *
monad_evsrc_any_from_aci(struct monad_evsrc_any_iter const *i)
{
    union monad_evsrc_const_any_iter_decoded u;
    switch (monad_evsrc_const_any_iter_decode(i, &u)) {
    case MONAD_EVSRC_EVENT_RING:
        return monad_evsrc_any_from_rci(u.ring_iter);
    case MONAD_EVSRC_EVCAP_SECTION:
        return monad_evsrc_any_from_cci(u.evcap_iter);
    default:
        __builtin_unreachable();
    }
}

/*
 * monad_evsrc_any_iter_from
 */

inline struct monad_evsrc_any_iter *
monad_evsrc_any_iter_from_ri(struct monad_event_ring_iter *iter)
{
    return (struct monad_evsrc_any_iter *)iter;
}

inline struct monad_evsrc_any_iter *
monad_evsrc_any_iter_from_ci(struct monad_evcap_event_iter *iter)
{
    uintptr_t const address = (uintptr_t)iter | 0b1;
    return (struct monad_evsrc_any_iter *)address;
}

inline struct monad_evsrc_any_iter *
monad_evsrc_any_iter_from_ai(struct monad_evsrc_any_iter *iter)
{
    return iter;
}

/*
 * monad_evsrc_iter_try_next
 */

inline monad_evsrc_result_t monad_evsrc_iter_try_next_ri(
    struct monad_event_ring_iter *iter, struct monad_event_descriptor *event,
    void const **payload)
{
    monad_event_ring_result_t const r =
        monad_event_ring_iter_try_next(iter, event);
    if (payload != nullptr) {
        struct monad_event_ring const *const event_ring = iter->event_ring;
        *payload = r == MONAD_EVENT_RING_SUCCESS &&
                           monad_event_ring_payload_check(event_ring, event)
                       ? monad_event_ring_payload_peek(event_ring, event)
                       : nullptr;
    }
    return (monad_evsrc_result_t)r;
}

inline monad_evsrc_result_t monad_evsrc_iter_try_next_ci(
    struct monad_evcap_event_iter *iter, struct monad_event_descriptor *event,
    void const **payload)
{
    struct monad_event_descriptor const *evcap_event;
    monad_evcap_read_result_t const r =
        monad_evcap_event_iter_next(iter, &evcap_event, payload);
    if (MONAD_LIKELY(r == MONAD_EVCAP_READ_SUCCESS)) {
        *event = *evcap_event;
    }
    return (monad_evsrc_result_t)r;
}

inline monad_evsrc_result_t monad_evsrc_iter_try_next_ai(
    struct monad_evsrc_any_iter *iter, struct monad_event_descriptor *event,
    void const **payload)
{
    union monad_evsrc_any_iter_decoded u;
    switch (monad_evsrc_any_iter_decode(iter, &u)) {
    case MONAD_EVSRC_EVENT_RING:
        return monad_evsrc_iter_try_next_ri(u.ring_iter, event, payload);
    case MONAD_EVSRC_EVCAP_SECTION:
        return monad_evsrc_iter_try_next_ci(u.evcap_iter, event, payload);
    default:
        __builtin_unreachable();
    }
}

/*
 * monad_evsrc_iter_try_prev
 */

inline monad_evsrc_result_t monad_evsrc_iter_try_prev_ri(
    struct monad_event_ring_iter *iter, struct monad_event_descriptor *event,
    void const **payload)
{
    monad_event_ring_result_t const r =
        monad_event_ring_iter_try_prev(iter, event);
    if (payload != nullptr) {
        struct monad_event_ring const *const event_ring = iter->event_ring;
        *payload = r == MONAD_EVENT_RING_SUCCESS &&
                           monad_event_ring_payload_check(event_ring, event)
                       ? monad_event_ring_payload_peek(event_ring, event)
                       : nullptr;
    }
    return (monad_evsrc_result_t)r;
}

inline monad_evsrc_result_t monad_evsrc_iter_try_prev_ci(
    struct monad_evcap_event_iter *iter, struct monad_event_descriptor *event,
    void const **payload)
{
    struct monad_event_descriptor const *evcap_event;
    monad_evcap_read_result_t const r =
        monad_evcap_event_iter_prev(iter, &evcap_event, payload);
    if (MONAD_LIKELY(r == MONAD_EVCAP_READ_SUCCESS)) {
        *event = *evcap_event;
    }
    return (monad_evsrc_result_t)r;
}

inline monad_evsrc_result_t monad_evsrc_iter_try_prev_ai(
    struct monad_evsrc_any_iter *iter, struct monad_event_descriptor *event,
    void const **payload)
{
    union monad_evsrc_any_iter_decoded u;
    switch (monad_evsrc_any_iter_decode(iter, &u)) {
    case MONAD_EVSRC_EVENT_RING:
        return monad_evsrc_iter_try_prev_ri(u.ring_iter, event, payload);
    case MONAD_EVSRC_EVCAP_SECTION:
        return monad_evsrc_iter_try_prev_ci(u.evcap_iter, event, payload);
    default:
        __builtin_unreachable();
    }
}

/*
 * monad_evsrc_iter_set_seqno
 */

inline monad_evsrc_result_t monad_evsrc_iter_set_seqno_ri(
    struct monad_event_ring_iter *iter, uint64_t seqno)
{
    monad_event_ring_iter_set_seqno(iter, seqno);
    return MONAD_EVSRC_SUCCESS;
}

inline monad_evsrc_result_t monad_evsrc_iter_set_seqno_ci(
    struct monad_evcap_event_iter *iter, uint64_t seqno)
{
    return (monad_evsrc_result_t)monad_evcap_event_iter_set_seqno(iter, seqno);
}

inline monad_evsrc_result_t
monad_evsrc_iter_set_seqno_ai(struct monad_evsrc_any_iter *iter, uint64_t seqno)
{
    union monad_evsrc_any_iter_decoded u;
    switch (monad_evsrc_any_iter_decode(iter, &u)) {
    case MONAD_EVSRC_EVENT_RING:
        return monad_evsrc_iter_set_seqno_ri(u.ring_iter, seqno);
    case MONAD_EVSRC_EVCAP_SECTION:
        return monad_evsrc_iter_set_seqno_ci(u.evcap_iter, seqno);
    default:
        __builtin_unreachable();
    }
}

/*
 * monad_evsrc_iter_seek
 */

inline void
monad_evsrc_iter_seek_ri(struct monad_event_ring_iter *iter, uint64_t position)
{
    monad_event_ring_iter_set_seqno(iter, position);
}

inline void
monad_evsrc_iter_seek_ci(struct monad_evcap_event_iter *iter, uint64_t position)
{
    iter->event_section_next = iter->event_section->section_base + position;
}

inline void
monad_evsrc_iter_seek_ai(struct monad_evsrc_any_iter *iter, uint64_t position)
{
    union monad_evsrc_any_iter_decoded u;
    switch (monad_evsrc_any_iter_decode(iter, &u)) {
    case MONAD_EVSRC_EVENT_RING:
        return monad_evsrc_iter_seek_ri(u.ring_iter, position);
    case MONAD_EVSRC_EVCAP_SECTION:
        return monad_evsrc_iter_seek_ci(u.evcap_iter, position);
    default:
        __builtin_unreachable();
    }
}

/*
 * monad_evsrc_iter_reset
 */

inline uint64_t monad_evsrc_iter_reset_ri(struct monad_event_ring_iter *iter)
{
    return monad_event_ring_iter_reset(iter);
}

inline uint64_t monad_evsrc_iter_reset_ci(struct monad_evcap_event_iter *iter)
{
    struct monad_event_descriptor const *evcap_event;
    return monad_evcap_event_iter_copy(iter, &evcap_event, nullptr)
               ? evcap_event->seqno
               : 0;
}

inline uint64_t monad_evsrc_iter_reset_ai(struct monad_evsrc_any_iter *iter)
{
    union monad_evsrc_any_iter_decoded u;
    switch (monad_evsrc_any_iter_decode(iter, &u)) {
    case MONAD_EVSRC_EVENT_RING:
        return monad_evsrc_iter_reset_ri(u.ring_iter);
    case MONAD_EVSRC_EVCAP_SECTION:
        return monad_evsrc_iter_reset_ci(u.evcap_iter);
    default:
        __builtin_unreachable();
    }
}

/*
 * monad_evsrc_const_any_iter_from
 */

inline struct monad_evsrc_any_iter const *
monad_evsrc_const_any_iter_from_ri(struct monad_event_ring_iter *iter)
{
    return monad_evsrc_any_iter_from_ri(iter);
}

inline struct monad_evsrc_any_iter const *
monad_evsrc_const_any_iter_from_ci(struct monad_evcap_event_iter *iter)
{
    return monad_evsrc_any_iter_from_ci(iter);
}

inline struct monad_evsrc_any_iter const *
monad_evsrc_const_any_iter_from_ai(struct monad_evsrc_any_iter *iter)
{
    return monad_evsrc_any_iter_from_ai(iter);
}

/*
 * monad_evsrc_iter_try_copy
 */

inline monad_evsrc_result_t monad_evsrc_iter_try_copy_rci(
    struct monad_event_ring_iter const *iter,
    struct monad_event_descriptor *event, void const **payload)
{
    monad_event_ring_result_t const r =
        monad_event_ring_iter_try_copy(iter, event);
    if (payload != nullptr) {
        struct monad_event_ring const *const event_ring = iter->event_ring;
        *payload = r == MONAD_EVENT_RING_SUCCESS &&
                           monad_event_ring_payload_check(event_ring, event)
                       ? monad_event_ring_payload_peek(event_ring, event)
                       : nullptr;
    }
    return (monad_evsrc_result_t)r;
}

inline monad_evsrc_result_t monad_evsrc_iter_try_copy_cci(
    struct monad_evcap_event_iter const *iter,
    struct monad_event_descriptor *event, void const **payload)
{
    struct monad_event_descriptor const *evcap_event;
    monad_evcap_read_result_t const r =
        monad_evcap_event_iter_copy(iter, &evcap_event, payload);
    if (MONAD_LIKELY(r == MONAD_EVCAP_READ_SUCCESS)) {
        *event = *evcap_event;
    }
    return (monad_evsrc_result_t)r;
}

inline monad_evsrc_result_t monad_evsrc_iter_try_copy_aci(
    struct monad_evsrc_any_iter const *iter,
    struct monad_event_descriptor *event, void const **payload)
{
    union monad_evsrc_const_any_iter_decoded u;
    switch (monad_evsrc_const_any_iter_decode(iter, &u)) {
    case MONAD_EVSRC_EVENT_RING:
        return monad_evsrc_iter_try_copy_rci(u.ring_iter, event, payload);
    case MONAD_EVSRC_EVCAP_SECTION:
        return monad_evsrc_iter_try_copy_cci(u.evcap_iter, event, payload);
    default:
        __builtin_unreachable();
    }
}

/*
 * monad_evsrc_iter_tell
 */

inline uint64_t
monad_evsrc_iter_tell_rci(struct monad_event_ring_iter const *iter)
{
    return iter->cur_seqno;
}

inline uint64_t
monad_evsrc_iter_tell_cci(struct monad_evcap_event_iter const *iter)
{
    return (uint64_t)(iter->event_section_next -
                      iter->event_section->section_base);
}

inline uint64_t
monad_evsrc_iter_tell_aci(struct monad_evsrc_any_iter const *iter)
{
    union monad_evsrc_const_any_iter_decoded u;
    switch (monad_evsrc_const_any_iter_decode(iter, &u)) {
    case MONAD_EVSRC_EVENT_RING:
        return monad_evsrc_iter_tell_rci(u.ring_iter);
    case MONAD_EVSRC_EVCAP_SECTION:
        return monad_evsrc_iter_tell_cci(u.evcap_iter);
    default:
        __builtin_unreachable();
    }
}

#ifdef __cplusplus
} // extern "C"
#endif
