#pragma once

#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include <sys/time.h>

#include <monad/event/event.h>
#include <monad/event/event_shmem.h>

#ifdef __cplusplus
extern "C"
{
#endif

/// Configuration options needed to connect to a monad event producer
struct monad_event_queue_options
{
    char const *socket_path; ///< Path to event server's UNIX domain socket
    struct timeval socket_timeout; ///< recvmsg(2) ETIMEDOUT if silent this long
    uint8_t ring_shift; ///< SPSC descriptor queue of size 1UL << ring_shift
};

struct monad_event_queue;

/// Create an event queue with the provided options. The initial domain mask
/// of the queue is zero, so no events will be received
int monad_event_queue_create(
    struct monad_event_queue_options const *, struct monad_event_queue **);

/// Destroy an event queue previously created with monad_event_queue_create
void monad_event_queue_destroy(struct monad_event_queue *);

/// Set the domain mask on the queue; this has a server-side effect, enabling
/// or disabling events from being posted to this queue
int monad_event_queue_set_domain_mask(
    struct monad_event_queue *, uint64_t desired_mask, uint64_t *recorder_mask,
    uint64_t *effective_mask, uint64_t *prev_mask);

/// Test whether the event server is still connected; this is an expensive
/// function (it requires a system call on the socket), so high performance
/// clients should not call this in a tight event polling loop
bool monad_event_queue_is_connected(struct monad_event_queue const *);

/// Get details about the last error that occurred on this thread
char const *monad_event_get_last_error();

/// Consume up to `num_events` event descriptors from the event queue and copy
/// them to the array pointed by `events`; the number of descriptors copied is
/// returned. If `num_available_events` is not nullptr, the number of events
/// that were available (which might be larger than `num_events`) will be
/// copied out, which can be used to detect back-pressure
static size_t monad_event_poll(
    struct monad_event_queue *queue, struct monad_event_descriptor *events,
    size_t num_events, size_t *num_available_events);

/// Obtain a pointer to the event's payload in shared memory; this may be
/// overwritten at any time, so the memory must be accessed quickly. The
/// validity of the memory accessed can be checked using the `page_generation`
/// variable; see the monad_event_memcpy implementation for more details
static void monad_event_mempeek(
    struct monad_event_queue const *queue,
    struct monad_event_descriptor const *evt, void **ptr,
    _Atomic(uint32_t) **page_generation);

/// Copy the event payload from shared memory into the supplied buffer, up to
/// `n` bytes; the total size required for an event is available using the
/// `length` field in the event descriptor; returns nullptr if the event
/// payload's memory has already been reused for a later event
static void *monad_event_memcpy(
    struct monad_event_queue const *queue,
    struct monad_event_descriptor const *evt, void *dst, size_t n);

#define MONAD_EVENT_CONSUMER_INTERNAL
#include "event_consumer_inline.h"
#undef MONAD_EVENT_CONSUMER_INTERNAL

#ifdef __cplusplus
} // extern "C"
#endif
