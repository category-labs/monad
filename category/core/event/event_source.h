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
 * This file defines the concepts of an "event source" and "event source
 * iterator", which can be used to write code that works with either:
 *
 *  - Event rings / event ring iterators
 *  - Event capture files / event section iterators
 *
 * A "source" corresponds to the object which provides the underlying memory
 * for the event descriptor and payload, and a "source iterator" knows how to
 * iterate through all the events in the source.
 *
 * This API also introduces a new kind of source called an "any" source
 * (struct monad_evsrc_any) and its iterator (struct monad_evsrc_any_iter). The
 * "any" source is a type-erased polymorphic source that can be used to write a
 * function which doesn't know what the underlying source type is.
 *
 * This API is polymorphic in two different dimensions:
 *
 *   - You can call a function with the same name that works with different
 *     concrete event source/iterator types (i.e. function overloading, a form
 *     of compile-time or "static" polymorphism); for example, calling
 *     `monad_evsrc_iter_try_next` will advance any kind of iterator
 *
 *   - You can use an explicit "any" source, which is an abstract type that
 *     acts as whatever source it actually is at runtime (dynamic polymorphism)
 *
 * This file provides both dimensions of polymorphism across C, C++, and Rust,
 * in a way that remains very "inline-able" for each compiler, similar to what
 * is possible with C++ templates. Code involving event iterators is performance
 * sensitive and we want the iteration logic to be inlined into the caller's
 * event loop.
 *
 * This makes the implementation verbose, see the full explanation of in the
 * `event_source_inline.h` file.
 *
 * To understand the API, be aware that the function prototypes don't exist in
 * a "simple" form in this header file, except in comments. Below you'll see a
 * comment like the following, and the comment "defines" an API function:
 *
 *     // bool monad_evsrc_check_payload(
 *     //    GENERIC_SOURCE, struct monad_event_descriptor const *);
 *
 * Here, "GENERIC_SOURCE" is a generic parameter (i.e., a type parameter in the
 * generic programming sense) which can be one of:
 *
 *  - An event ring (struct monad_event_ring const *)
 *  - An evcap file event section (struct monad_evcap_event_section const *)
 *  - An abstract "any source" (struct monad_evsrc_any const *)
 *
 * What this header actually does is declare (via macros) the underlying
 * "specializations" of the various API functions for all three kinds of event
 * sources, which follow a particular name-mangling scheme, e.g., the
 * functionality of the above "generic signature" corresponds to these three
 * concrete functions:
 *
 *   - monad_evsrc_check_payload_r for event rings
 *   - monad_evsrc_check_payload_c for evcap sections
 *   - monad_evsrc_check_payload_a for an "any" source
 *
 * The file `event_ring_inline.h` provides all the implementations of these.
 * The static polymorphism is re-implemented in each language: in C++, one line
 * function overload wrappers forward to corresponding suffixed function (in
 * `event_source_inline_cxx.hpp`). In C, a _Generic expression in a function
 * macro selects the correct function (in `event_source_inline_c_generic.h`).
 * In Rust, the work is done via trait implementations that call the correct
 * function.
 */

#include <stdint.h>

struct monad_evcap_event_section;
struct monad_event_ring;
struct monad_evsrc_any;

struct monad_evcap_event_iter;
struct monad_event_descriptor;
struct monad_event_ring_iter;
struct monad_evsrc_any_iter;

#ifdef __cplusplus
extern "C"
{
#endif

typedef enum monad_evsrc_type
{
    MONAD_EVSRC_EVENT_RING,
    MONAD_EVSRC_EVCAP_SECTION
} monad_evsrc_type_t;

/// Result of trying to read an event descriptor and payload from an event
/// source; these combine the possible numerical codes of for
/// monad_event_ring_result_t and monad_evcap_read_result_t
typedef enum monad_evsrc_result
    : uint16_t
{
    MONAD_EVSRC_SUCCESS = 0,
    MONAD_EVSRC_NOT_READY = 0x0100,
    MONAD_EVSRC_GAP = 0x0101,
    MONAD_EVSRC_END = 0x0200,
    MONAD_EVSRC_NO_SEQNO = 0x0201,
} monad_evsrc_result_t;

static monad_evsrc_type_t
monad_evsrc_any_get_type(struct monad_evsrc_any const *);

static monad_evsrc_type_t
monad_evsrc_any_iter_get_type(struct monad_evsrc_any_iter const *);

#define MONAD_SDK_EVSRC_DECL(RETURN, NAME, ...)                                \
    static RETURN NAME##_r(struct monad_event_ring const *__VA_OPT__(, )       \
                               __VA_ARGS__);                                   \
    static RETURN NAME##_c(                                                    \
        struct monad_evcap_event_section const *__VA_OPT__(, ) __VA_ARGS__);   \
    static RETURN NAME##_a(struct monad_evsrc_any const *__VA_OPT__(, )        \
                               __VA_ARGS__);

#define MONAD_SDK_EVSRC_ITER_DECL(RETURN, NAME, ...)                           \
    static RETURN NAME##_ri(struct monad_event_ring_iter *__VA_OPT__(, )       \
                                __VA_ARGS__);                                  \
    static RETURN NAME##_ci(struct monad_evcap_event_iter *__VA_OPT__(, )      \
                                __VA_ARGS__);                                  \
    static RETURN NAME##_ai(struct monad_evsrc_any_iter *__VA_OPT__(, )        \
                                __VA_ARGS__);

#define MONAD_SDK_EVSRC_CONST_ITER_DECL(RETURN, NAME, ...)                     \
    static RETURN NAME##_rci(                                                  \
        struct monad_event_ring_iter const *__VA_OPT__(, ) __VA_ARGS__);       \
    static RETURN NAME##_cci(                                                  \
        struct monad_evcap_event_iter const *__VA_OPT__(, ) __VA_ARGS__);      \
    static RETURN NAME##_aci(struct monad_evsrc_any_iter const *__VA_OPT__(, ) \
                                 __VA_ARGS__);

/*
 * bool monad_evsrc_check_payload(
 *     GENERIC_SOURCE, struct monad_event_descriptor const *);
 */

typedef bool(monad_evsrc_check_payload_fn_t)(
    void const *, struct monad_event_descriptor const *);

MONAD_SDK_EVSRC_DECL(
    bool, monad_evsrc_check_payload, struct monad_event_descriptor const *)

/*
 * monad_evsrc_result_t
 * monad_evsrc_copy_seqno(GENERIC_SOURCE, uint64_t seqno,
 *     struct monad_event_descriptor *, void const **payload);
 */

typedef monad_evsrc_result_t(monad_evsrc_copy_seqno_fn_t)(
    void const *, uint64_t, struct monad_event_descriptor *, void const **);

MONAD_SDK_EVSRC_DECL(
    monad_evsrc_result_t, monad_evsrc_copy_seqno, uint64_t,
    struct monad_event_descriptor *, void const **)

/*
 * void monad_evsrc_close(GENERIC_SOURCE);
 */

typedef void(monad_evsrc_close_fn_t)(void *);

static void monad_evsrc_close_r(struct monad_event_ring *);
static void monad_evsrc_close_c(struct monad_evcap_event_section *);
static void monad_evsrc_close_a(struct monad_evsrc_any *);

/*
 * struct monad_evsrc_any const *monad_evsrc_any_from(GENERIC_SOURCE);
 * struct monad_evsrc_any const *monad_evsrc_any_from(CONST_GENERIC_ITER);
 */

typedef struct monad_evsrc_any const *(monad_evsrc_any_from_fn_t)(void const *);

MONAD_SDK_EVSRC_DECL(struct monad_evsrc_any const *, monad_evsrc_any_from)
MONAD_SDK_EVSRC_CONST_ITER_DECL(
    struct monad_evsrc_any const *, monad_evsrc_any_from)

/*
 * struct monad_evsrc_any_iter *monad_evsrc_any_iter_from(GENERIC_ITER);
 */

typedef struct monad_evsrc_any_iter *(monad_evsrc_any_iter_from_fn_t)(void *);

MONAD_SDK_EVSRC_ITER_DECL(
    struct monad_evsrc_any_iter *, monad_evsrc_any_iter_from)

/*
 * monad_evsrc_result_t
 * monad_evsrc_iter_try_next(GENERIC_ITER, struct monad_event_descriptor *,
 *     void const **payload);
 */

typedef monad_evsrc_result_t(monad_evsrc_iter_try_next_fn_t)(
    void *, struct monad_event_descriptor *, void const **payload);

MONAD_SDK_EVSRC_ITER_DECL(
    enum monad_evsrc_result, monad_evsrc_iter_try_next,
    struct monad_event_descriptor *, void const **)

/*
 * monad_evsrc_result_t
 * monad_evsrc_iter_try_prev(GENERIC_ITER, struct monad_event_descriptor *,
 *     void const **payload);
 */

typedef monad_evsrc_result_t(monad_evsrc_iter_try_prev_fn_t)(
    void *, struct monad_event_descriptor *, void const **payload);

MONAD_SDK_EVSRC_ITER_DECL(
    monad_evsrc_result_t, monad_evsrc_iter_try_prev,
    struct monad_event_descriptor *, void const **)

/*
 * int monad_evsrc_iter_set_seqno(GENERIC_ITER, uint64_t seqno);
 */

typedef monad_evsrc_result_t(monad_evsrc_iter_set_seqno_fn_t)(void *, uint64_t);

MONAD_SDK_EVSRC_ITER_DECL(
    monad_evsrc_result_t, monad_evsrc_iter_set_seqno, uint64_t)

/*
 * void monad_evsrc_iter_seek(GENERIC_ITER, uint64_t position);
 */

typedef void(monad_evsrc_iter_seek_fn_t)(void *, uint64_t);

MONAD_SDK_EVSRC_ITER_DECL(void, monad_evsrc_iter_seek, uint64_t)

/*
 * uint64_t monad_evsrc_iter_reset(GENERIC_ITER);
 */

typedef uint64_t(monad_evsrc_iter_reset_fn_t)(void *);

MONAD_SDK_EVSRC_ITER_DECL(uint64_t, monad_evsrc_iter_reset)

/*
 * struct monad_evsrc_any_iter const *
 *     monad_evsrc_const_any_iter_from(GENERIC_ITER);
 */

typedef struct monad_evsrc_any_iter const *(
    monad_evsrc_const_any_iter_from_fn_t)(void *);

MONAD_SDK_EVSRC_ITER_DECL(
    struct monad_evsrc_any_iter const *, monad_evsrc_const_any_iter_from)

/*
 * monad_evsrc_result_t monad_evsrc_iter_try_copy(GENERIC_CONST_ITER,
 *     struct monad_event_descriptor *, void const **payload);
 */

typedef monad_evsrc_result_t(monad_evsrc_iter_try_copy_fn_t)(
    void const *, struct monad_event_descriptor *, void const **);

MONAD_SDK_EVSRC_CONST_ITER_DECL(
    monad_evsrc_result_t, monad_evsrc_iter_try_copy,
    struct monad_event_descriptor *, void const **)

/*
 * uint64_t monad_evsrc_iter_tell(GENERIC_CONST_ITER);
 */

typedef uint64_t(monad_evsrc_iter_tell_fn_t)(void const *);

MONAD_SDK_EVSRC_CONST_ITER_DECL(uint64_t, monad_evsrc_iter_tell)

struct monad_evsrc_ops
{
    monad_evsrc_check_payload_fn_t *const check_payload;
    monad_evsrc_copy_seqno_fn_t *const copy_seqno;
    monad_evsrc_close_fn_t *const close;
};

struct monad_evsrc_iter_ops
{
    monad_evsrc_iter_try_next_fn_t *const try_next;
    monad_evsrc_iter_try_prev_fn_t *const try_prev;
    monad_evsrc_iter_set_seqno_fn_t *const set_seqno;
    monad_evsrc_iter_seek_fn_t *const seek;
    monad_evsrc_iter_reset_fn_t *const reset;
    monad_evsrc_iter_try_copy_fn_t *const try_copy;
    monad_evsrc_iter_tell_fn_t *const tell;
};

#define MONAD_DEFINE_EVSRC_OPS(NAME, SUFFIX)                                   \
    struct monad_evsrc_ops const NAME = {                                      \
        .check_payload = (monad_evsrc_check_payload_fn_t *)                    \
            monad_evsrc_check_payload_##SUFFIX,                                \
        .copy_seqno =                                                          \
            (monad_evsrc_copy_seqno_fn_t *)monad_evsrc_copy_seqno_##SUFFIX,    \
        .close = (monad_evsrc_close_fn_t *)monad_evsrc_close_##SUFFIX};

#define MONAD_DEFINE_EVSRC_ITER_OPS(NAME, SUFFIX)                              \
    struct monad_evsrc_iter_ops const NAME = {                                 \
        .try_next = (monad_evsrc_iter_try_next_fn_t *)                         \
            monad_evsrc_iter_try_next_##SUFFIX##i,                             \
        .try_prev = (monad_evsrc_iter_try_prev_fn_t *)                         \
            monad_evsrc_iter_try_prev_##SUFFIX##i,                             \
        .set_seqno = (monad_evsrc_iter_set_seqno_fn_t *)                       \
            monad_evsrc_iter_set_seqno_##SUFFIX##i,                            \
        .seek =                                                                \
            (monad_evsrc_iter_seek_fn_t *)monad_evsrc_iter_seek_##SUFFIX##i,   \
        .reset =                                                               \
            (monad_evsrc_iter_reset_fn_t *)monad_evsrc_iter_reset_##SUFFIX##i, \
        .try_copy = (monad_evsrc_iter_try_copy_fn_t *)                         \
            monad_evsrc_iter_try_copy_##SUFFIX##ci,                            \
        .tell =                                                                \
            (monad_evsrc_iter_tell_fn_t *)monad_evsrc_iter_tell_##SUFFIX##ci};

#ifdef __cplusplus
} // extern "C"
#endif

#define MONAD_EVENT_SOURCE_INTERNAL

#include "event_source_inline.h"

#ifdef __cplusplus
    #include "event_source_inline_cxx.hpp"
#else
    #include "event_source_inline_c_generic.h"
#endif

#undef MONAD_EVENT_SOURCE_INTERNAL
