#pragma once

/**
 * @file
 *
 * Event recorder interface. There are four things in this file:
 *
 *   1. The macros and functions used for recording events and taking
 *      timestamps. These are needed by any file that wishes to record events.
 *
 *   2. The initialization function to configure the recorders -- setting
 *      the amount of memory for the recorder descriptor table and payload
 *      buffer -- and a function to enable/disable a recorder gracefully
 *
 *   3. Minimum, maximum, and default values for various memory configuration
 *      options
 *
 *   4. Functions related to managing the block flow ID mapping and the active
 *      transaction ID
 */

#include <stdint.h>
#include <sys/uio.h>

#include <monad/event/event.h>

#ifdef __cplusplus
extern "C"
{
#endif

enum monad_event_metadata_type : uint8_t;
struct monad_event_iterator;

/// Special behavior flags used in the `MONAD_EVENT` family of recording
/// macros; the typical value is zero, i.e., no special behavior
enum monad_event_flags : uint8_t
{
    MONAD_EVENT_POP_SCOPE = 0b1 ///< Set pop_scope=1 in descriptor (for tracer)
};

/// Record an event with the given type and flags, whose event payload is
/// described by the given (PTR, SIZE) pair that will be memcpy'ed to the
/// payload buffer
#define MONAD_EVENT_MEMCPY(EVENT_TYPE, FLAGS, PTR, SIZE)                       \
    monad_event_record(                                                        \
        &g_monad_event_recorders[MONAD_EVENT_RING_EXEC],                       \
        (EVENT_TYPE),                                                          \
        (FLAGS),                                                               \
        (PTR),                                                                 \
        (SIZE))

/// Record an event with the given type and flags, whose event payload is
/// described by the given l-value expression
#define MONAD_EVENT_EXPR(EVENT_TYPE, FLAGS, LEXPR)                             \
    MONAD_EVENT_MEMCPY((EVENT_TYPE), (FLAGS), &(LEXPR), sizeof(LEXPR))

/// Record an event  with the given type and flags, whose event payload is
/// described by given `struct iovec` array (as an iovec pointer and length
/// pair)
#define MONAD_EVENT_IOV(EVENT_TYPE, FLAGS, IOV, IOVLEN)                        \
    monad_event_recordv(                                                       \
        &g_monad_event_recorders[MONAD_EVENT_RING_EXEC],                       \
        (EVENT_TYPE),                                                          \
        (FLAGS),                                                               \
        (IOV),                                                                 \
        (IOVLEN))

/// Record an event with an empty payload
#define MONAD_EVENT(EVENT_TYPE, FLAGS)                                         \
    MONAD_EVENT_MEMCPY((EVENT_TYPE), (FLAGS), nullptr, 0)

struct monad_event_recorder;

/// Initialize an event recorder's memory allocation parameters; this must be
/// called prior to the recorder being enabled, otherwise it will have no
/// effect and will return EBUSY
int monad_event_recorder_configure(
    enum monad_event_ring_type ring_type, uint8_t ring_shift,
    uint8_t payload_buf_shift);

/// Start or stop the recorder for the given event ring type; disabling a
/// recorder will allow monad_event_recorder_configure to be called again
static bool
monad_event_recorder_set_enabled(enum monad_event_ring_type, bool enabled);

/// Return a description of the last recorder error that occurred on this thread
char const *monad_event_recorder_get_last_error();

/// Take a timestamp, in nanoseconds since the UNIX epoch
static uint64_t monad_event_get_epoch_nanos();

/// Take a timestamp, using a clock known to the recording infrastructure;
/// it will be translated to epoch nanos before being seen by consumers
static uint64_t monad_event_timestamp();

/// Record an event; usually invoked via the `MONAD_EVENT_` or `MONAD_TRACE_`
/// family of macros
static void monad_event_record(
    struct monad_event_recorder *recorder, enum monad_event_type event_type,
    uint8_t flags, void const *payload, size_t payload_size);

/// Record an event with "gather I/O", similar to writev(2); usually invoked
/// via the `MONAD_EVENT_IOV` or `MONAD_TRACE_IOV` macros
static void monad_event_recordv(
    struct monad_event_recorder *recorder, enum monad_event_type event_type,
    uint8_t flags, struct iovec const *iov, size_t iovlen);

/// Allocate a new block flow object in the execution recorder
static struct monad_event_block_exec_header *
monad_event_recorder_alloc_block_exec_header();

/// Publish a BLOCK_START event with the given block execution header; sets
/// the block flow ID as a side-effect
static void
monad_event_recorder_start_block(struct monad_event_block_exec_header const *);

/// Publish a BLOCK_END event with the given block result structure; clears
/// the block flow ID as a side-effect
static void
monad_event_recorder_end_block(struct monad_event_block_exec_result const *);

/// Obtains information about the event ID metadata locations (used to
/// implement the MONAD_EVENT_MSG_METADATA_OFFSET protocol message in the
/// server)
int monad_event_recorder_export_metadata_section(
    enum monad_event_metadata_type, uint32_t *offset);

/// Initialize an event reader that runs in the same process as the recorder;
/// external processes use a special library, see libs/event/event.md
int monad_event_init_local_iterator(
    enum monad_event_ring_type, struct monad_event_iterator *);

/// __attribute__((constructor)) priority of the event recorders' constructor
#define MONAD_EVENT_RECORDER_CTOR_PRIO 1000

/*
 * Min, max, and default memory sizes
 */

#define MONAD_EVENT_DEFAULT_EXEC_RING_SHIFT (20)
#define MONAD_EVENT_MIN_EXEC_RING_SHIFT (16)
#define MONAD_EVENT_MAX_EXEC_RING_SHIFT (32)

#define MONAD_EVENT_DEFAULT_EXEC_PAYLOAD_BUF_SHIFT (28)
#define MONAD_EVENT_MIN_EXEC_PAYLOAD_BUF_SHIFT (27)
#define MONAD_EVENT_MAX_EXEC_PAYLOAD_BUF_SHIFT (40)

#define MONAD_EVENT_RECORDER_INTERNAL
#include "event_recorder_inline.h"
#undef MONAD_EVENT_RECORDER_INTERNAL

#ifdef __cplusplus
} // extern "C"
#endif
