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
#include <monad/event/event_iterator.h>
#include <monad/event/event_recorder.h>

constexpr uint64_t MaxPerfIterations = 1UL << 20;

static void perf_consumer_main(std::latch *latch)
{
    constexpr size_t EventDelayHistogramSize = 30;
    constexpr size_t EventsAvailableHistogramSize = 20;

    monad_event_iterator iterator;
    monad_event_descriptor events[16];

    ASSERT_EQ(
        0,
        monad_event_init_local_iterator(
            MONAD_EVENT_RING_EXEC, &iterator, nullptr));
    uint64_t last_seqno = monad_event_iterator_reset(&iterator);
    uint64_t expected_counter = 0;
    uint64_t delay_histogram[EventDelayHistogramSize] = {};
    uint64_t available_histogram[EventsAvailableHistogramSize] = {};

    latch->arrive_and_wait();
    while (true) {
        size_t num_events = std::size(events);
        size_t available_events;
        monad_event_poll_result const pr = monad_event_iterator_bulk_copy(
            &iterator, events, &num_events, &available_events);
        if (MONAD_UNLIKELY(pr == MONAD_EVENT_NOT_READY)) {
            continue;
        }
        ASSERT_EQ(MONAD_EVENT_READY, pr);

        // Available histogram
        unsigned avail_bucket =
            static_cast<unsigned>(std::bit_width(available_events));
        if (avail_bucket >= std::size(available_histogram)) {
            avail_bucket = std::size(available_histogram) - 1;
        }
        ++available_histogram[avail_bucket];

        for (monad_event_descriptor const &event_desc :
             std::span{events, num_events}) {
            // TODO(ken): should be monad_event_get_epoch_nanos(), when we
            //   fix timestamp RDTSC support
            auto const delay = monad_event_timestamp() - event_desc.epoch_nanos;
            unsigned delay_bucket =
                static_cast<unsigned>(std::bit_width(delay));
            if (delay_bucket >= std::size(delay_histogram)) {
                delay_bucket = std::size(delay_histogram) - 1;
            }
            ++delay_histogram[delay_bucket];
            EXPECT_EQ(last_seqno + 1, event_desc.seqno);
            last_seqno = event_desc.seqno;

            std::atomic<uint64_t> const *overwrite_seqno;
            if (MONAD_UNLIKELY(event_desc.type != MONAD_EVENT_TEST_COUNT_64)) {
                continue;
            }
            uint64_t const counter_value =
                *static_cast<uint64_t const *>(monad_event_payload_peek(
                    &iterator, &event_desc, &overwrite_seqno));
            ASSERT_GE(
                event_desc.seqno,
                overwrite_seqno->load(std::memory_order::acquire));
            EXPECT_EQ(expected_counter++, counter_value);
            expected_counter = counter_value + 1;
            ASSERT_EQ(event_desc.length, sizeof counter_value);
            if (last_seqno >= MaxPerfIterations - 1) {
                fprintf(stdout, "backpressure histogram:\n");
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

                fprintf(stdout, "delay histogram:\n");
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

TEST(event_recorder, perf_test_bulk)
{
    using std::chrono::duration_cast, std::chrono::nanoseconds;

    std::latch sync_latch{2};
    monad_event_recorder_set_enabled(MONAD_EVENT_RING_EXEC, true);
    std::thread consumer_thread{perf_consumer_main, &sync_latch};
    sync_latch.arrive_and_wait();
    sleep(1);

    auto const start_time = std::chrono::system_clock::now();
    for (uint64_t counter = 0; counter < MaxPerfIterations; ++counter) {
        MONAD_EVENT_EXPR(MONAD_EVENT_TEST_COUNT_64, 0, counter);
    }
    auto const end_time = std::chrono::system_clock::now();
    auto const elapsed_nanos = static_cast<uint64_t>(
        duration_cast<nanoseconds>(end_time - start_time).count());
    std::fprintf(
        stdout,
        "recording speed: %lu ns/evt %lu iterations in %ld\n",
        elapsed_nanos / MaxPerfIterations,
        MaxPerfIterations,
        elapsed_nanos);
    consumer_thread.join();
}
