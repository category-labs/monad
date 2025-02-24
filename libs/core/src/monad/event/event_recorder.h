#pragma once

/**
 * @file
 *
 * Event recorder interface. There are three things in this file:
 *
 *   1. The macros and functions used for recording events and taking
 *      timestamps. These are needed by any file that wishes to record events
 *
 *   2. Functions to configure and enable/disable the event ring recorder
 *      objects
 *
 *   3. Functions for managing the block flow ID
 */

#include <stddef.h>
#include <stdint.h>

enum monad_event_ring_type : uint8_t;
enum monad_event_type : uint16_t;

struct iovec;
struct monad_event_block_exec_header;
struct monad_event_recorder;
struct monad_event_ring_db;

#ifdef __cplusplus
extern "C"
{
#endif

/*
 * Recording functions and macros
 */

/// Special behavior flags used in the `MONAD_EVENT` family of recording
/// macros; the typical value is zero, i.e., no special behavior
enum monad_event_flags : uint8_t
{
    MONAD_EVENT_POP_SCOPE = 0b1 ///< Set pop_scope in descriptor (for tracer)
};

/// Record an event with the given type and flags to the execution ring; the
/// event payload is described by the given (PTR, SIZE) pair
#define MONAD_EVENT_MEMCPY(EVENT_TYPE, FLAGS, PTR, SIZE)                       \
    monad_event_record(                                                        \
        &g_monad_event_recorders[MONAD_EVENT_RING_EXEC],                       \
        (EVENT_TYPE),                                                          \
        (FLAGS),                                                               \
        (PTR),                                                                 \
        (SIZE))

/// Record an event with the given type and flags to the execution ring; the
/// event payload is described by the given l-value expression
#define MONAD_EVENT_EXPR(EVENT_TYPE, FLAGS, LEXPR)                             \
    MONAD_EVENT_MEMCPY((EVENT_TYPE), (FLAGS), &(LEXPR), sizeof(LEXPR))

/// Record an event with the given type and flags to the execution ring; the
/// event payload is described by the given `struct iovec` array (as an iovec
/// pointer and length pair)
#define MONAD_EVENT_IOV(EVENT_TYPE, FLAGS, IOV, IOVLEN)                        \
    monad_event_recordv(                                                       \
        &g_monad_event_recorders[MONAD_EVENT_RING_EXEC],                       \
        (EVENT_TYPE),                                                          \
        (FLAGS),                                                               \
        (IOV),                                                                 \
        (IOVLEN))

/// Record an event with an empty payload to the execution ring
#define MONAD_EVENT(EVENT_TYPE, FLAGS)                                         \
    MONAD_EVENT_MEMCPY((EVENT_TYPE), (FLAGS), nullptr, 0)

/// Take a timestamp, in nanoseconds since the UNIX epoch
static uint64_t monad_event_get_epoch_nanos();

/// Record an event; this function is not usually called directly, but via the
/// `MONAD_EVENT_` or `MONAD_TRACE_` family of recording macros
static void monad_event_record(
    struct monad_event_recorder *, enum monad_event_type, uint8_t flags,
    void const *payload, size_t payload_size);

/// Record an event with "gather I/O", similar to writev(2); usually called by
/// the `MONAD_EVENT_IOV` or `MONAD_TRACE_IOV` macros
static void monad_event_recordv(
    struct monad_event_recorder *, enum monad_event_type, uint8_t flags,
    struct iovec const *iov, size_t iovlen);

/*
 * Event recorder configuration
 */

/// Init function that must be called prior to any other, to configure the
/// process for event recording; this creates the ring db file with shm_open(2)
int monad_event_recorder_system_init(
    char const *shm_name, struct monad_event_ring_db **);

/// Set an event recorder's memory allocation parameters; this must be called
/// prior to the recorder being enabled, otherwise it will have no effect and
/// will return EBUSY
int monad_event_recorder_configure(
    struct monad_event_ring_db *, enum monad_event_ring_type,
    uint8_t ring_shift, uint8_t payload_buf_shift);

/// Start or stop the recorder for the given event ring type; disabling a
/// recorder allows monad_event_recorder_configure to be called again; the
/// recorder must already be configured in order to enable it
static bool
monad_event_recorder_set_enabled(enum monad_event_ring_type, bool enabled);

/// Directly return a mapped event ring; returns nullptr if the event ring is
/// not enabled; this can be used to initialize readers in the same process
/// that is hosting the writer
struct monad_event_ring const *monad_event_recorder_get_event_ring(
    struct monad_event_ring_db *, enum monad_event_ring_type);

/// Return a description of the last recorder error that occurred on this thread
char const *monad_event_recorder_get_last_error();

/// __attribute__((constructor)) priority of the event recorders' constructor
#define MONAD_EVENT_RECORDER_CTOR_PRIO 1000

/*
 * Min, max, and default memory sizes -- the "shift" means the power of two
 * exponent, e.g., a ring_shift of 20 means 2^20 (or 1 << 20)
 */

#define MONAD_EVENT_DEFAULT_EXEC_RING_SHIFT (20)
#define MONAD_EVENT_MIN_EXEC_RING_SHIFT (16)
#define MONAD_EVENT_MAX_EXEC_RING_SHIFT (32)

#define MONAD_EVENT_DEFAULT_EXEC_PAYLOAD_BUF_SHIFT (28)
#define MONAD_EVENT_MIN_EXEC_PAYLOAD_BUF_SHIFT (27)
#define MONAD_EVENT_MAX_EXEC_PAYLOAD_BUF_SHIFT (40)

/*
 * Block flow ID management functions
 */

/// Return the next block flow ID and activate it in all recorders; subsequent
/// recorded events will carry this block flow ID until it is explicitly
/// cleared; also return the block execution header array slot (in the metadata
/// page) that corresponds to this ID
static uint16_t
monad_event_next_block_flow_id(struct monad_event_block_exec_header **);

/// Clear the active block flow ID set by `monad_event_alloc_block_flow_id`
static void monad_event_clear_block_flow_id();

#define MONAD_EVENT_RECORDER_INTERNAL
#include "event_recorder_inline.h"
#undef MONAD_EVENT_RECORDER_INTERNAL

#ifdef __cplusplus
} // extern "C"
#endif
