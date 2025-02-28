#pragma once

/**
 * @file
 *
 * Event recorder interface. Recorders are the objects that own event ring
 * shared memory files, and are able to write new event data into them. This
 * interface allows you to create and destroy recorders, and to record events.
 */

#include <stddef.h>
#include <stdint.h>

#include <sys/queue.h>

#include <monad/event/event.h>

struct iovec;
struct monad_event_recorder;

#ifdef __cplusplus
extern "C"
{
#endif

/*
 * Recording functions
 */

/// Record an event whose payload is in a single contiguous buffer
static void monad_event_record(
    struct monad_event_recorder *, enum monad_event_type, void const *payload,
    size_t payload_size);

/// Record an event with "gather I/O", similar to writev(2)
static void monad_event_recordv(
    struct monad_event_recorder *, enum monad_event_type,
    struct iovec const *iov, size_t iovlen);

/// Take a timestamp, in nanoseconds since the UNIX epoch
static uint64_t monad_event_get_epoch_nanos();

/*
 * Event recorder management functions
 */

// clang-format off

/// Event recorder configuration parameters; passed at event recorder creation
struct monad_event_recorder_config
{
    char const *file_path;     ///< Event ring's shared memory file
    off_t ring_file_offset;    ///< Offset in file where we create event ring
    int open_flags;            ///< open(2) flags for ring fd
    mode_t create_mode;        ///< open(2) mode for ring fd
    bool unlink_after_close;   ///< True -> unlink(2) file_path when we die
    uint8_t descriptors_shift; ///< # of event ring descriptors == 1 << shift
    uint8_t payload_buf_shift; ///< Payload buffer size == 1 << shift
};

// clang-format on

#define MONAD_EVENT_MIN_DESCRIPTORS_SHIFT (16)
#define MONAD_EVENT_MAX_DESCRIPTORS_SHIFT (32)

#define MONAD_EVENT_MIN_PAYLOAD_BUF_SHIFT (27)
#define MONAD_EVENT_MAX_PAYLOAD_BUF_SHIFT (40)

/// Create an event recorder with the given parameters
int monad_event_recorder_create(
    struct monad_event_recorder **, struct monad_event_recorder_config const *);

/// Destroy an event recorder
void monad_event_recorder_destroy(struct monad_event_recorder *);

/// __attribute__((constructor)) priority of the static constructor
#define MONAD_EVENT_RECORDER_CTOR_PRIO 1000

// clang-format off

struct monad_event_recorder
{
    struct monad_event_ring event_ring;  ///< Event ring owned by recorder
    struct monad_event_ring_control *control; ///< Cached ring control pointer
    size_t desc_capacity_mask;           ///< Event descriptor capacity - 1
    size_t payload_buf_mask;             ///< Payload buffer size - 1
    char const *file_path;               ///< Path to event ring file
    int ring_fd;                         ///< Open fd; holds OFD lock in place
    bool unlink_file_at_close;           ///< True -> unlink(file_path) at death
    off_t ring_file_offset;              ///< Event ring at this offset in file
    size_t total_ring_bytes;             ///< Total size of ring in file
    TAILQ_ENTRY(monad_event_recorder) next; ///< Linkage for all recorders list
};

// clang-format on

#define MONAD_EVENT_RECORDER_INTERNAL
#include "event_recorder_inline.h"
#undef MONAD_EVENT_RECORDER_INTERNAL

#ifdef __cplusplus
} // extern "C"
#endif
