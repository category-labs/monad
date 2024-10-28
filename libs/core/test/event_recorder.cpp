#include <atomic>
#include <bit>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <latch>
#include <span>
#include <thread>

#include <gtest/gtest.h>
#include <monad/core/likely.h>
#include <monad/event/event.h>
#include <monad/event/event_recorder.h>
#include <monad/event/event_session.h>
#include <monad/event/event_shmem.h>

constexpr uint64_t MaxPerfIterations = 1UL << 20;

static void perf_consumer_main(monad_event_ring *ring, std::latch *latch)
{
    constexpr size_t EventDelayHistogramSize = 30;
    constexpr size_t EventsAvailableHistogramSize = 20;

    monad_event_descriptor events[16];
    size_t page_pool_size;

    monad_event_payload_page **all_payload_pages =
        _monad_event_get_payload_page_pool_array(&page_pool_size);
    std::span const pages{all_payload_pages, page_pool_size};
    uint64_t last_seqno = 0;
    uint64_t expected_counter = 0;
    uint64_t delay_histogram[EventDelayHistogramSize] = {};
    uint64_t available_histogram[EventsAvailableHistogramSize] = {};

    latch->arrive_and_wait();
    while (true) {
        size_t available_events;
        unsigned bucket;
        size_t const num_events = monad_event_ring_read_descriptors(
            ring, events, std::size(events), &available_events);

        // Available histogram
        bucket = static_cast<unsigned>(std::bit_width(available_events));
        if (bucket >= std::size(available_histogram)) {
            bucket = std::size(available_histogram) - 1;
        }
        ++available_histogram[bucket];

        for (monad_event_descriptor const &event_desc :
             std::span{events, num_events}) {
            // TODO(ken): should be monad_event_get_epoch_nanos(), when we
            //   fix timestamp RDTSC support
            auto const delay = monad_event_timestamp() - event_desc.epoch_nanos;
            unsigned bucket = static_cast<unsigned>(std::bit_width(delay));
            if (bucket >= std::size(delay_histogram)) {
                bucket = std::size(delay_histogram) - 1;
            }
            ++delay_histogram[bucket];
            EXPECT_EQ(last_seqno + 1, event_desc.seqno);
            last_seqno = event_desc.seqno;
            monad_event_payload_page const *const pp =
                pages[event_desc.payload_page];
            if (MONAD_UNLIKELY(event_desc.type == MONAD_EVENT_SYNC_EVENT_GAP)) {
                monad_event_sync_gap const gap_info =
                    *std::bit_cast<monad_event_sync_gap const *>(
                        std::bit_cast<std::byte const *>(pp) +
                        event_desc.offset);
                fprintf(
                    stdout,
                    "GAP: %lu -> %lu : %hu at %lu\n",
                    gap_info.last_seqno,
                    gap_info.event.seqno,
                    gap_info.event.type,
                    gap_info.event.epoch_nanos);
                ASSERT_NE(MONAD_EVENT_SYNC_EVENT_GAP, event_desc.type);
            }
            if (MONAD_UNLIKELY(event_desc.type != MONAD_EVENT_TEST_COUNT_64)) {
                continue;
            }
            uint64_t const counter_value = *std::bit_cast<uint64_t const *>(
                std::bit_cast<std::byte const *>(pp) + event_desc.offset);
            EXPECT_EQ(
                atomic_load_explicit(
                    &pp->page_header.page_generation, memory_order_acquire),
                event_desc.page_generation);
            EXPECT_EQ(expected_counter++, counter_value);
            expected_counter = counter_value + 1;
            ASSERT_EQ(event_desc.length, sizeof counter_value);
            if (last_seqno >= MaxPerfIterations - 1) {
                fprintf(stdout, "SPSC backpressure histogram:\n");
                for (size_t b = 0; uint64_t const v :
                                   std::span{available_histogram}.subspan(1)) {
                    fprintf(
                        stdout,
                        "%7lu - %7lu %lu\n",
                        1UL << b,
                        (1UL << (b + 1)) - 1,
                        v);
                    ++b;
                }

                fprintf(stdout, "SPSC delay histogram:\n");
                for (size_t b = 0;
                     uint64_t const v : std::span{delay_histogram}.subspan(1)) {
                    fprintf(
                        stdout,
                        "%7lu - %7lu %lu\n",
                        1UL << b,
                        (1UL << (b + 1)) - 1,
                        v);
                    ++b;
                }
                return;
            }
        }
    }
}

TEST(event_recorder, perf_test)
{
    using std::chrono::duration_cast, std::chrono::nanoseconds;
    monad_event_recorder_set_domain_mask(MONAD_EVENT_DOMAIN_INTERNAL);

    monad_event_session *session;
    monad_event_session_open(0, &session);
    ASSERT_NE(session, nullptr);
    monad_event_session_set_domain_mask(session, MONAD_EVENT_DOMAIN_INTERNAL);

    std::latch sync_latch{2};
    std::thread consumer_thread{
        perf_consumer_main, &session->event_ring, &sync_latch};
    sync_latch.arrive_and_wait();
    sleep(1);

    std::atomic_thread_fence(std::memory_order::seq_cst);
    auto const start_time = std::chrono::system_clock::now();
    for (uint64_t counter = 0; counter < MaxPerfIterations; ++counter) {
        MONAD_EVENT_EXPR(MONAD_EVENT_TEST_COUNT_64, 0, counter);
    }
    auto const end_time = std::chrono::system_clock::now();
    std::atomic_thread_fence(std::memory_order::seq_cst);
    auto const elapsed_nanos = static_cast<uint64_t>(
        duration_cast<nanoseconds>(end_time - start_time).count());
    std::fprintf(
        stdout,
        "recording speed: %lu ns/evt %lu iterations in %ld\n",
        elapsed_nanos / MaxPerfIterations,
        MaxPerfIterations,
        elapsed_nanos);
    consumer_thread.join();

    monad_event_session_close(session);
}
