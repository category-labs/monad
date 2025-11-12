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
 * This file defines generic functions in C using macros and the _Generic
 * facility from C99; for C++ (which does not support _Generic) function
 * overloads are used instead
 */

#define monad_exec_get_block_number(SOURCE, ...)                               \
    _Generic(                                                                  \
        (SOURCE),                                                              \
        struct monad_event_ring *: monad_exec_get_block_number_r,              \
        struct monad_event_ring const *: monad_exec_get_block_number_r,        \
        struct monad_evcap_event_section *: monad_exec_get_block_number_c,     \
        struct monad_evcap_event_section const                                 \
            *: monad_exec_get_block_number_c,                                  \
        struct monad_evsrc_any *: monad_exec_get_block_number_a,               \
        struct monad_evsrc_any const *: monad_exec_get_block_number_a)(        \
        (SOURCE)__VA_OPT__(, ) __VA_ARGS__)

#define monad_exec_get_block_id(SOURCE, ...)                                   \
    _Generic(                                                                  \
        (SOURCE),                                                              \
        struct monad_event_ring *: monad_exec_get_block_id_r,                  \
        struct monad_event_ring const *: monad_exec_get_block_id_r,            \
        struct monad_evcap_event_section *: monad_exec_get_block_id_c,         \
        struct monad_evcap_event_section const *: monad_exec_get_block_id_c,   \
        struct monad_evsrc_any *: monad_exec_get_block_id_a,                   \
        struct monad_evsrc_any const *: monad_exec_get_block_id_a)(            \
        (SOURCE)__VA_OPT__(, ) __VA_ARGS__)

#define monad_exec_iter_consensus_prev(ITER, ...)                              \
    _Generic(                                                                  \
        (ITER),                                                                \
        struct monad_event_ring_iter *: monad_exec_iter_consensus_prev_ri,     \
        struct monad_evcap_event_iter *: monad_exec_iter_consensus_prev_ci,    \
        struct monad_evsrc_any_iter *: monad_exec_iter_consensus_prev_ai)(     \
        (ITER)__VA_OPT__(, ) __VA_ARGS__)

#define monad_exec_iter_block_number_prev(ITER, ...)                           \
    _Generic(                                                                  \
        (ITER),                                                                \
        struct monad_event_ring_iter *: monad_exec_iter_block_number_prev_ri,  \
        struct monad_evcap_event_iter *: monad_exec_iter_block_number_prev_ci, \
        struct monad_evsrc_any_iter *: monad_exec_iter_block_number_prev_ai)(  \
        (ITER)__VA_OPT__(, ) __VA_ARGS__)

#define monad_exec_iter_block_id_prev(ITER, ...)                               \
    _Generic(                                                                  \
        (ITER),                                                                \
        struct monad_event_ring_iter *: monad_exec_iter_block_id_prev_ri,      \
        struct monad_evcap_event_iter *: monad_exec_iter_block_id_prev_ci,     \
        struct monad_evsrc_any_iter *: monad_exec_iter_block_id_prev_ai)(      \
        (ITER)__VA_OPT__(, ) __VA_ARGS__)

#define monad_exec_iter_rewind_for_simple_replay(ITER, ...)                        \
    _Generic(                                                                      \
        (ITER),                                                                    \
        struct                                                                     \
            monad_event_ring_iter *: monad_exec_iter_rewind_for_simple_replay_ri,  \
        struct                                                                     \
            monad_evcap_event_iter *: monad_exec_iter_rewind_for_simple_replay_ci, \
        struct                                                                     \
            monad_evsrc_any_iter *: monad_exec_iter_rewind_for_simple_replay_ai)(  \
        (ITER)__VA_OPT__(, ) __VA_ARGS__)
