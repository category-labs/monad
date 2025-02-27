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

/// Event ring configuration parameters; passed at event recorder creation
struct monad_event_recorder_config
{
    char const *file_path;     ///< Event ring's shared memory file
    uint8_t ring_shift;        ///< # of event ring descriptors == 1 << shift
    uint8_t payload_buf_shift; ///< Payload buffer size == 1 << shift
};

// clang-format on

#define MONAD_EVENT_MIN_RING_SHIFT (16)
#define MONAD_EVENT_MAX_RING_SHIFT (32)

#define MONAD_EVENT_MIN_PAYLOAD_BUF_SHIFT (27)
#define MONAD_EVENT_MAX_PAYLOAD_BUF_SHIFT (40)

/// Create an event recorder with the given parameters
int monad_event_recorder_create(
    struct monad_event_recorder **, struct monad_event_recorder_config const *);

/// Destroy an event recorder
void monad_event_recorder_destroy(struct monad_event_recorder *);

/// __attribute__((constructor)) priority of the static constructor
#define MONAD_EVENT_RECORDER_CTOR_PRIO 1000

struct monad_event_recorder
{
    struct monad_event_ring event_ring;
    struct monad_event_ring_control *control;
    size_t capacity_mask;
    size_t payload_buf_mask;
    char const *file_path;
    int ring_fd;
    TAILQ_ENTRY(monad_event_recorder) next;
};

#define MONAD_EVENT_RECORDER_INTERNAL
#include "event_recorder_inline.h"
#undef MONAD_EVENT_RECORDER_INTERNAL

#ifdef __cplusplus
} // extern "C"
#endif
