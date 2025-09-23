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
 * This file defines generic functions in C using macros and the _Generic
 * facility from C99; for C++ (which does not support _Generic) function
 * overloads are used instead
 */

#define monad_evsrc_check_payload(SOURCE, ...)                                 \
    _Generic(                                                                  \
        (SOURCE),                                                              \
        struct monad_event_ring *: monad_evsrc_check_payload_r,                \
        struct monad_event_ring const *: monad_evsrc_check_payload_r,          \
        struct monad_evcap_event_section *: monad_evsrc_check_payload_c,       \
        struct monad_evcap_event_section const *: monad_evsrc_check_payload_c, \
        struct monad_evsrc_any *: monad_evsrc_check_payload_a,                 \
        struct monad_evsrc_any const *: monad_evsrc_check_payload_a)(          \
        (SOURCE)__VA_OPT__(, ) __VA_ARGS__)

#define monad_evsrc_copy_seqno(SOURCE, ...)                                    \
    _Generic(                                                                  \
        (SOURCE),                                                              \
        struct monad_event_ring *: monad_evsrc_copy_seqno_r,                   \
        struct monad_event_ring const *: monad_evsrc_copy_seqno_r,             \
        struct monad_evcap_event_section *: monad_evsrc_copy_seqno_c,          \
        struct monad_evcap_event_section const *: monad_evsrc_copy_seqno_c,    \
        struct monad_evsrc_any *: monad_evsrc_copy_seqno_a,                    \
        struct monad_evsrc_any const *: monad_evsrc_copy_seqno_a)(             \
        (SOURCE)__VA_OPT__(, ) __VA_ARGS__)

#define monad_evsrc_close(SOURCE)                                              \
    _Generic(                                                                  \
        (SOURCE),                                                              \
        struct monad_event_ring *: monad_evsrc_close_r,                        \
        struct monad_evcap_event_section *: monad_evsrc_close_c,               \
        struct monad_evsrc_any *: monad_evsrc_close_a)((SOURCE))

#define monad_evsrc_any_from(SOURCE, ...)                                      \
    _Generic(                                                                  \
        (SOURCE),                                                              \
        struct monad_event_ring *: monad_evsrc_any_from_r,                     \
        struct monad_event_ring const *: monad_evsrc_any_from_r,               \
        struct monad_evcap_event_section *: monad_evsrc_any_from_c,            \
        struct monad_evcap_event_section const *: monad_evsrc_any_from_c,      \
        struct monad_evsrc_any *: monad_evsrc_any_from_a,                      \
        struct monad_evsrc_any const *: monad_evsrc_any_from_a,                \
        struct monad_event_ring_iter *: monad_evsrc_any_from_rci,              \
        struct monad_event_ring_iter const *: monad_evsrc_any_from_rci,        \
        struct monad_evcap_event_iter *: monad_evsrc_any_from_cci,             \
        struct monad_evcap_event_iter const *: monad_evsrc_any_from_cci,       \
        struct monad_evsrc_any_iter *: monad_evsrc_any_from_aci,               \
        struct monad_evsrc_any_iter const *: monad_evsrc_any_from_aci)(        \
        (SOURCE)__VA_OPT__(, ) __VA_ARGS__)

#define monad_evsrc_any_iter_from(ITER, ...)                                   \
    _Generic(                                                                  \
        (ITER),                                                                \
        struct monad_event_ring_iter *: monad_evsrc_any_iter_from_ri,          \
        struct monad_evcap_event_iter *: monad_evsrc_any_iter_from_ci,         \
        struct monad_evsrc_any_iter *: monad_evsrc_any_iter_from_ai)(          \
        (ITER)__VA_OPT__(, ) __VA_ARGS__)

#define monad_evsrc_iter_try_next(ITER, ...)                                   \
    _Generic(                                                                  \
        (ITER),                                                                \
        struct monad_event_ring_iter *: monad_evsrc_iter_try_next_ri,          \
        struct monad_evcap_event_iter *: monad_evsrc_iter_try_next_ci,         \
        struct monad_evsrc_any_iter *: monad_evsrc_iter_try_next_ai)(          \
        (ITER)__VA_OPT__(, ) __VA_ARGS__)

#define monad_evsrc_iter_try_prev(ITER, ...)                                   \
    _Generic(                                                                  \
        (ITER),                                                                \
        struct monad_event_ring_iter *: monad_evsrc_iter_try_prev_ri,          \
        struct monad_evcap_event_iter *: monad_evsrc_iter_try_prev_ci,         \
        struct monad_evsrc_any_iter *: monad_evsrc_iter_try_prev_ai)(          \
        (ITER)__VA_OPT__(, ) __VA_ARGS__)

#define monad_evsrc_iter_set_seqno(ITER, ...)                                  \
    _Generic(                                                                  \
        (ITER),                                                                \
        struct monad_event_ring_iter *: monad_evsrc_iter_set_seqno_ri,         \
        struct monad_evcap_event_iter *: monad_evsrc_iter_set_seqno_ci,        \
        struct monad_evsrc_any_iter *: monad_evsrc_iter_set_seqno_ai)(         \
        (ITER)__VA_OPT__(, ) __VA_ARGS__)

#define monad_evsrc_iter_seek(ITER, ...)                                       \
    _Generic(                                                                  \
        (ITER),                                                                \
        struct monad_event_ring_iter *: monad_evsrc_iter_seek_ri,              \
        struct monad_evcap_event_iter *: monad_evsrc_iter_seek_ci,             \
        struct monad_evsrc_any_iter *: monad_evsrc_iter_seek_ai)(              \
        (ITER)__VA_OPT__(, ) __VA_ARGS__)

#define monad_evsrc_iter_reset(ITER, ...)                                      \
    _Generic(                                                                  \
        (ITER),                                                                \
        struct monad_event_ring_iter *: monad_evsrc_iter_reset_ri,             \
        struct monad_evcap_event_iter *: monad_evsrc_iter_reset_ci,            \
        struct monad_evsrc_any_iter *: monad_evsrc_iter_reset_ai)(             \
        (ITER)__VA_OPT__(, ) __VA_ARGS__)

#define monad_evsrc_const_any_iter_from(ITER, ...)                             \
    _Generic(                                                                  \
        (ITER),                                                                \
        struct monad_event_ring_iter *: monad_evsrc_const_any_iter_from_ri,    \
        struct monad_event_ring_iter const                                     \
            *: monad_evsrc_const_any_iter_from_ri,                             \
        struct monad_evcap_event_iter *: monad_evsrc_const_any_iter_from_ci,   \
        struct monad_evcap_event_iter const                                    \
            *: monad_evsrc_const_any_iter_from_ci,                             \
        struct monad_evsrc_any_iter *: monad_evsrc_const_any_iter_from_ai,     \
        struct monad_evsrc_any_iter const                                      \
            *: monad_evsrc_const_any_iter_from_ai)((ITER)__VA_OPT__(, )        \
                                                       __VA_ARGS__)

#define monad_evsrc_iter_try_copy(ITER, ...)                                   \
    _Generic(                                                                  \
        (ITER),                                                                \
        struct monad_event_ring_iter *: monad_evsrc_iter_try_copy_rci,         \
        struct monad_event_ring_iter const *: monad_evsrc_iter_try_copy_rci,   \
        struct monad_evcap_event_iter *: monad_evsrc_iter_try_copy_cci,        \
        struct monad_evcap_event_iter const *: monad_evsrc_iter_try_copy_cci,  \
        struct monad_evsrc_any_iter *: monad_evsrc_iter_try_copy_aci,          \
        struct monad_evsrc_any_iter const *: monad_evsrc_iter_try_copy_aci)(   \
        (ITER)__VA_OPT__(, ) __VA_ARGS__)

#define monad_evsrc_iter_tell(ITER, ...)                                       \
    _Generic(                                                                  \
        (ITER),                                                                \
        struct monad_event_ring_iter *: monad_evsrc_iter_tell_rci,             \
        struct monad_event_ring_iter const *: monad_evsrc_iter_tell_rci,       \
        struct monad_evcap_event_iter *: monad_evsrc_iter_tell_cci,            \
        struct monad_evcap_event_iter const *: monad_evsrc_iter_tell_cci,      \
        struct monad_evsrc_any_iter *: monad_evsrc_iter_tell_aci,              \
        struct monad_evsrc_any_iter const *: monad_evsrc_iter_tell_aci)(       \
        (ITER)__VA_OPT__(, ) __VA_ARGS__)
