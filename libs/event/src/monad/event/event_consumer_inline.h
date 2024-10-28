#ifndef MONAD_EVENT_CONSUMER_INTERNAL
    #error This file should only be included directly by event_consumer.h
#endif

#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include <monad/event/event.h>
#include <monad/event/event_shmem.h>

// clang-format off

struct monad_event_payload_page
{
    struct monad_event_payload_page_header *page_header;
    size_t map_len;
};

struct monad_event_queue
{
    pthread_spinlock_t lock;
    int sock_fd;
    uint16_t payload_page_size;
    uint16_t payload_page_capacity;
    uint64_t domain_mask;
    struct monad_event_payload_page *payload_pages;
    struct monad_event_ring event_ring;
};

// clang-format on

inline size_t monad_event_poll(
    struct monad_event_queue *queue, struct monad_event_descriptor *events,
    size_t num_events, size_t *num_available_events)
{
    return monad_event_ring_read_descriptors(
        &queue->event_ring, events, num_events, num_available_events);
}

inline void monad_event_mempeek(
    struct monad_event_queue const *queue,
    struct monad_event_descriptor const *evt, void **ptr,
    _Atomic(uint32_t) **page_generation)
{
    struct monad_event_payload_page *const page =
        &queue->payload_pages[evt->payload_page];
    *ptr = (uint8_t *)page->page_header + evt->offset;
    *page_generation = &page->page_header->page_generation;
}

inline void *monad_event_memcpy(
    struct monad_event_queue const *queue,
    struct monad_event_descriptor const *evt, void *dst, size_t n)
{
    _Atomic(uint32_t) *page_generation;
    void *src;

    monad_event_mempeek(queue, evt, &src, &page_generation);
    memcpy(dst, src, n);
    if (__builtin_expect(
            atomic_load_explicit(page_generation, memory_order_acquire) !=
                evt->page_generation,
            0)) {
        // The shared memory page this payload lives in has been reused by
        // later events. We didn't copy this fast enough to be sure that all
        // `copy_size` bytes are valid.
        return nullptr;
    }
    return dst;
}
