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

static void perf_consumer_main(std::latch *latch, uint64_t expected_len)
{
    constexpr size_t EventDelayHistogramSize = 30;
    constexpr size_t EventsAvailableHistogramSize = 20;
    constexpr unsigned HistogramShift = 10;
    constexpr uint64_t HistogramSampleMask = (1UL << HistogramShift) - 1;

    monad_event_iterator iter{};
    ASSERT_EQ(0, monad_event_init_local_iterator(MONAD_EVENT_RING_EXEC, &iter));
    uint64_t expected_counter = 0;
    uint64_t delay_histogram[EventDelayHistogramSize] = {};
    uint64_t available_histogram[EventsAvailableHistogramSize] = {};

    latch->arrive_and_wait();
    // TODO(ken): this should not be necessary
    while (__atomic_load_n(iter.seqno_fragment_next, __ATOMIC_ACQUIRE) == 0 ||
           __atomic_load_n(iter.seqno_fragment_next, __ATOMIC_ACQUIRE) ==
               (__uint128_t)1 << 64)
        /* wait for something to be produced */;
    monad_event_iterator_reset(&iter);
    // Regardless of where the most recent event is, start from zero
    uint64_t last_seqno = iter.last_seqno = iter.next_fragment = 0;
    while (last_seqno < MaxPerfIterations) {
        monad_event_fragment const *begin;
        monad_event_fragment const *end;
        monad_event_poll_result const pr =
            monad_event_iterator_peek(&iter, &begin, &end);
        if (MONAD_UNLIKELY(
                pr == MONAD_EVENT_NOT_READY || pr == MONAD_EVENT_PARTIAL)) {
            continue;
        }
        ASSERT_EQ(MONAD_EVENT_READY, pr);

        // Available histogram
        if (MONAD_UNLIKELY((last_seqno & HistogramSampleMask) == 0)) {
            uint64_t next_seqno =
                (uint64_t)(__atomic_load_n(
                               iter.seqno_fragment_next, __ATOMIC_ACQUIRE) >>
                           64);
            uint64_t const available_events = next_seqno - begin->header.seqno;
            unsigned avail_bucket =
                static_cast<unsigned>(std::bit_width(available_events));
            if (avail_bucket >= std::size(available_histogram)) {
                avail_bucket = std::size(available_histogram) - 1;
            }
            ++available_histogram[avail_bucket];

            // TODO(ken): should be monad_event_get_epoch_nanos(), when we
            //   fix timestamp RDTSC support
            auto const delay =
                monad_event_timestamp() - begin->header.epoch_nanos;
            unsigned delay_bucket =
                static_cast<unsigned>(std::bit_width(delay));
            if (delay_bucket >= std::size(delay_histogram)) {
                delay_bucket = std::size(delay_histogram) - 1;
            }
            ++delay_histogram[delay_bucket];
        }
        EXPECT_EQ(last_seqno + 1, begin->header.seqno);
        last_seqno = begin->header.seqno;

        if (MONAD_UNLIKELY(begin->header.type != MONAD_EVENT_TEST_COUNT_64)) {
            ASSERT_TRUE(monad_event_iterator_advance(&iter, begin));
            continue;
        }
        uint64_t const counter_value =
            *std::bit_cast<uint64_t const *>(&begin->payload[0]);
        EXPECT_EQ(expected_counter++, counter_value);
        expected_counter = counter_value + 1;
        ASSERT_EQ(begin->header.total_length, expected_len);

        ASSERT_TRUE(monad_event_iterator_advance(&iter, begin));
    }

    fprintf(stdout, "backpressure histogram:\n");
    for (size_t b = 0;
         uint64_t const v : std::span{available_histogram}.subspan(1)) {
        fprintf(stdout, "%7lu - %7lu %lu\n", 1UL << b, (1UL << (b + 1)) - 1, v);
        ++b;
    }

    fprintf(stdout, "delay histogram:\n");
    for (size_t b = 0;
         uint64_t const v : std::span{delay_histogram}.subspan(1)) {
        fprintf(stdout, "%7lu - %7lu %lu\n", 1UL << b, (1UL << (b + 1)) - 1, v);
        ++b;
    }
}

class EventRecorderBulkTest : public testing::TestWithParam<uint32_t>
{
    void SetUp() override
    {
        monad_event_recorder_set_enabled(MONAD_EVENT_RING_EXEC, false);
        monad_event_recorder_configure(
            MONAD_EVENT_RING_EXEC, MONAD_EVENT_DEFAULT_RING_SHIFT);
    }
};

TEST_P(EventRecorderBulkTest, )
{
    using std::chrono::duration_cast, std::chrono::nanoseconds;
    std::byte payload_buf[1 << 14];

    std::latch sync_latch{2};
    uint32_t const payload_len = GetParam();
    uint64_t *const write = std::bit_cast<uint64_t *>(&payload_buf[0]);
    monad_event_recorder_set_enabled(MONAD_EVENT_RING_EXEC, true);
    std::thread consumer_thread{perf_consumer_main, &sync_latch, payload_len};
    sync_latch.arrive_and_wait();
    sleep(1);

    auto const start_time = std::chrono::system_clock::now();
    for (uint64_t counter = 0; counter < MaxPerfIterations; ++counter) {
        *write = counter;
        MONAD_EVENT_MEMCPY(
            MONAD_EVENT_TEST_COUNT_64, 0, payload_buf, payload_len);
    }
    auto const end_time = std::chrono::system_clock::now();
    auto const elapsed_nanos = static_cast<uint64_t>(
        duration_cast<nanoseconds>(end_time - start_time).count());
    std::fprintf(
        stdout,
        "recording speed: %lu ns/evt of payload size %u [%lu iterations in "
        "%ld]\n",
        elapsed_nanos / MaxPerfIterations,
        payload_len,
        MaxPerfIterations,
        elapsed_nanos);
    consumer_thread.join();
}

INSTANTIATE_TEST_SUITE_P(
    perf_test_bulk, EventRecorderBulkTest,
    testing::Values(8, 128, 512, 1024, 8192));
