#pragma once

/**
 * @file
 *
 * This file defines the data structures that live in shared memory segments
 * and are mapped into the address space of both the producer and consumer
 * processes. It also contains some inline functions that operate on them.
 */

#include <assert.h>
#include <stdatomic.h>
#include <stdbit.h>
#include <stddef.h>
#include <string.h>

#include <monad/event/event.h>

#ifdef __cplusplus
extern "C"
{
#endif

#define MONAD_EVENT_CONSUMER_DEFAULT_RING_SHIFT (20)

/// Maximum number of events that can be copied out in a single call to
/// monad_event_ring_read_descriptors
#define MONAD_EVENT_MAX_EVENTS                                                 \
    ((1UL << 21) / sizeof(struct monad_event_descriptor))

struct monad_event_ring_control;

/// An IPC-style ring used to implement a lock-free SPSC queue for passing
/// event descriptors between threads, potentially in different processes.
/// This object is not directly present in shared memory, but the control page
/// and descriptor table are.
struct monad_event_ring
{
    struct monad_event_ring_control *control;
    struct monad_event_descriptor *descriptor_table;
    size_t capacity_mask;
    size_t capacity;
    int control_fd;
    int descriptor_table_fd;
};

/// Control registers of the SPSC ring, mapped in a shared memory page
struct monad_event_ring_control
{
    alignas(64) _Atomic(uint64_t) prod_next;
    alignas(64) _Atomic(uint64_t) consume_next;
};

/// Header object present at offset zero of a shared payload page
struct monad_event_payload_page_header
{
    alignas(64) _Atomic(uint32_t) page_generation;
    uint16_t page_id;
    uint16_t : 16;
};

/// Thread metadata; this is the event payload of the MONAD_EVENT_THREAD_CREATE
/// event type, and it lives on a payload page that is never recycled
struct monad_event_thread_info
{
    uint64_t seqno;
    uint64_t epoch_nanos;
    uint64_t process_id;
    uint64_t thread_id;
    uint8_t source_id;
    char thread_name[31];
};

/// Consume up to `num_events` event descriptors from the event ring and copy
/// them to the array pointed by `events`; the number of descriptors copied is
/// returned. If `num_available_events` is not nullptr, the number of events
/// that were available (which might be larger than `num_events`) will be
/// copied out, which can be used to detect back-pressure
static inline size_t monad_event_ring_read_descriptors(
    struct monad_event_ring *ring, struct monad_event_descriptor *events,
    size_t num_events, size_t *num_available_events)
{
    size_t available;
    assert(num_events < MONAD_EVENT_MAX_EVENTS);
    if (num_available_events == nullptr) {
        num_available_events = &available;
    }
    uint64_t const consume_next = atomic_load_explicit(
        &ring->control->consume_next, memory_order_relaxed);
    uint64_t const prod_next =
        atomic_load_explicit(&ring->control->prod_next, memory_order_acquire);
    *num_available_events = prod_next - consume_next;
    num_events =
        num_events < *num_available_events ? num_events : *num_available_events;
    memcpy(
        events,
        &ring->descriptor_table[consume_next & ring->capacity_mask],
        sizeof events[0] * num_events);
    atomic_store_explicit(
        &ring->control->consume_next,
        consume_next + num_events,
        memory_order_relaxed);
    return num_events;
}

/// Write an event descriptor to the ring
static inline void monad_event_ring_write_descriptor(
    struct monad_event_ring *ring, struct monad_event_descriptor *event)
{
    uint64_t const prod_next =
        atomic_load_explicit(&ring->control->prod_next, memory_order_relaxed);
    uint64_t const prod_next_inc = prod_next + 1;
    event->seqno = prod_next_inc;
    ring->descriptor_table[prod_next & ring->capacity_mask] = *event;
    atomic_store_explicit(
        &ring->control->prod_next, prod_next_inc, memory_order_release);
}

#ifdef __cplusplus
} // extern "C"
#endif
