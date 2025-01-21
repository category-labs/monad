#include <atomic>
#include <bit>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <latch>
#include <span>
#include <thread>
#include <tuple>
#include <vector>

#include <pthread.h>
#include <sched.h>
#include <unistd.h>

#include <gtest/gtest.h>
#include <monad/core/likely.h>
#include <monad/core/spinloop.h>
#include <monad/event/event.h>
#include <monad/event/event_iterator.h>
#include <monad/event/event_recorder.h>
#include <monad/event/event_types.h>

constexpr uint64_t MaxPerfIterations = 1UL << 20;

// Running the tests with the reader disabled is a good measure of how
// expensive the multi-threaded lock-free recording in the writer is, without
// any potential synchronization effects of a reader.
constexpr bool ENABLE_READER = true;
constexpr bool DISPLAY_HISTOGRAMS = false;

static bool alloc_cpu(cpu_set_t *avail_cpus, cpu_set_t *out)
{
    int const n_cpus = CPU_COUNT(avail_cpus);
    CPU_ZERO(out);
    for (int c = 0; c < n_cpus; ++c) {
        if (CPU_ISSET(c, avail_cpus)) {
            CPU_CLR(c, avail_cpus);
            CPU_SET(c, out);
            return true;
        }
    }
    return false;
}

static void writer_main(
    std::latch *latch, uint8_t writer_id, uint8_t writer_thread_count,
    uint32_t payload_size)
{
    using std::chrono::duration_cast, std::chrono::nanoseconds;
    std::byte payload_buf[1 << 14]{};

    uint64_t const writer_iterations = MaxPerfIterations / writer_thread_count;
    auto *const test_counter =
        std::bit_cast<monad_event_test_counter *>(&payload_buf[0]);
    test_counter->writer_id = writer_id;
    latch->arrive_and_wait();
    sleep(1);
    auto const start_time = std::chrono::system_clock::now();
    for (uint64_t counter = 0; counter < writer_iterations; ++counter) {
        test_counter->counter = counter;
        MONAD_EVENT_MEMCPY(
            MONAD_EVENT_TEST_COUNTER, 0, payload_buf, payload_size);
    }
    auto const end_time = std::chrono::system_clock::now();
    auto const elapsed_nanos = static_cast<uint64_t>(
        duration_cast<nanoseconds>(end_time - start_time).count());
    std::fprintf(
        stdout,
        "writer %hhu recording speed: %lu ns/evt of payload size %u "
        "[%lu iterations in %ld]\n",
        writer_id,
        elapsed_nanos / writer_iterations,
        payload_size,
        writer_iterations,
        elapsed_nanos);
}

[[maybe_unused]] static void reader_main(
    std::latch *latch, uint8_t writer_thread_count, uint32_t expected_len)
{
    constexpr size_t EventDelayHistogramSize = 30;
    constexpr size_t EventsAvailableHistogramSize = 20;
    constexpr unsigned HistogramShift = 10;
    constexpr uint64_t HistogramSampleMask = (1UL << HistogramShift) - 1;

    uint64_t const max_writer_iteration =
        MaxPerfIterations / writer_thread_count;
    monad_event_iterator iter{};
    std::vector<uint64_t> expected_counters;
    expected_counters.resize(writer_thread_count, 0);
    ASSERT_EQ(0, monad_event_init_local_iterator(MONAD_EVENT_RING_EXEC, &iter));
    uint64_t delay_histogram[EventDelayHistogramSize] = {};
    uint64_t available_histogram[EventsAvailableHistogramSize] = {};

    latch->arrive_and_wait();
    std::atomic_ref const write_last_seqno{*iter.write_last_seqno};
    // Wait for something to be produced
    while (write_last_seqno.load(std::memory_order_acquire) == 0) {
        monad_spinloop_hint();
    }
    monad_event_iterator_reset(&iter);
    // Regardless of where the most recent event is, start from zero
    uint64_t last_seqno = iter.read_last_seqno = 0;
    while (last_seqno < max_writer_iteration) {
        monad_event_descriptor event;
        monad_event_next_result const nr =
            monad_event_iterator_try_next(&iter, &event);
        if (MONAD_UNLIKELY(nr == MONAD_EVENT_NOT_READY)) {
            monad_spinloop_hint();
            continue;
        }
        ASSERT_EQ(MONAD_EVENT_SUCCESS, nr);

        // Available histogram
        if (MONAD_UNLIKELY((last_seqno + 1) & HistogramSampleMask) == 0) {
            uint64_t const available_events =
                write_last_seqno.load(std::memory_order::acquire) - event.seqno;
            unsigned avail_bucket =
                static_cast<unsigned>(std::bit_width(available_events));
            if (avail_bucket >= std::size(available_histogram)) {
                avail_bucket = std::size(available_histogram) - 1;
            }
            ++available_histogram[avail_bucket];

            // TODO(ken): should be monad_event_get_epoch_nanos(), when we
            //   fix timestamp RDTSC support
            auto const delay = monad_event_timestamp() - event.epoch_nanos;
            unsigned delay_bucket =
                static_cast<unsigned>(std::bit_width(delay));
            if (delay_bucket >= std::size(delay_histogram)) {
                delay_bucket = std::size(delay_histogram) - 1;
            }
            ++delay_histogram[delay_bucket];
        }
        EXPECT_EQ(last_seqno + 1, event.seqno);
        last_seqno = event.seqno;

        if (MONAD_UNLIKELY(event.type != MONAD_EVENT_TEST_COUNTER)) {
            continue;
        }
        ASSERT_EQ(event.length, expected_len);
        auto const test_counter =
            *static_cast<monad_event_test_counter const *>(
                monad_event_payload_peek(&iter, &event));
        ASSERT_TRUE(monad_event_payload_check(&iter, &event));
        ASSERT_GT(writer_thread_count, test_counter.writer_id);
        EXPECT_EQ(
            expected_counters[test_counter.writer_id], test_counter.counter);
        expected_counters[test_counter.writer_id] = test_counter.counter + 1;
    }

    if constexpr (DISPLAY_HISTOGRAMS) {
        fprintf(stdout, "backpressure histogram:\n");
        for (size_t b = 0;
             uint64_t const v : std::span{available_histogram}.subspan(1)) {
            fprintf(
                stdout, "%7lu - %7lu %lu\n", 1UL << b, (1UL << (b + 1)) - 1, v);
            ++b;
        }

        fprintf(stdout, "delay histogram:\n");
        for (size_t b = 0;
             uint64_t const v : std::span{delay_histogram}.subspan(1)) {
            fprintf(
                stdout, "%7lu - %7lu %lu\n", 1UL << b, (1UL << (b + 1)) - 1, v);
            ++b;
        }
    }
}

class EventRecorderBulkTest
    : public testing::TestWithParam<std::tuple<uint8_t, uint32_t>>
{
    void SetUp() override
    {
        monad_event_recorder_set_enabled(MONAD_EVENT_RING_EXEC, false);
        monad_event_recorder_configure(
            MONAD_EVENT_RING_EXEC,
            MONAD_EVENT_DEFAULT_EXEC_RING_SHIFT,
            MONAD_EVENT_DEFAULT_EXEC_PAYLOAD_BUF_SHIFT);
    }
};

TEST_P(EventRecorderBulkTest, )
{
    auto const [writer_thread_count, payload_size] = GetParam();
    std::latch sync_latch{writer_thread_count + (ENABLE_READER ? 2 : 1)};
    std::vector<std::thread> writer_threads;
    cpu_set_t avail_cpus, thr_cpu;

    ASSERT_EQ(
        0,
        pthread_getaffinity_np(pthread_self(), sizeof avail_cpus, &avail_cpus));
    monad_event_recorder_set_enabled(MONAD_EVENT_RING_EXEC, true);
    for (uint8_t t = 0; t < writer_thread_count; ++t) {
        char name[16];
        snprintf(name, sizeof name, "writer-%hhu", t);
        ASSERT_TRUE(alloc_cpu(&avail_cpus, &thr_cpu));
        auto &thread = writer_threads.emplace_back(
            writer_main, &sync_latch, t, writer_thread_count, payload_size);
        auto const thr = thread.native_handle();
        pthread_setname_np(thr, name);
        ASSERT_EQ(0, pthread_setaffinity_np(thr, sizeof thr_cpu, &thr_cpu));
    }
    std::thread reader_thread;

    if constexpr (ENABLE_READER) {
        ASSERT_TRUE(alloc_cpu(&avail_cpus, &thr_cpu));
        reader_thread = std::thread{
            reader_main, &sync_latch, writer_thread_count, payload_size};
        auto const thr = reader_thread.native_handle();
        pthread_setname_np(thr, "reader");
        ASSERT_EQ(0, pthread_setaffinity_np(thr, sizeof thr_cpu, &thr_cpu));
    }
    sync_latch.arrive_and_wait();
    for (auto &thr : writer_threads) {
        thr.join();
    }
    if (reader_thread.joinable()) {
        reader_thread.join();
    }
}

// Running the full test every time is too slow
#if RUN_FULL_EVENT_RECORDER_TEST
INSTANTIATE_TEST_SUITE_P(
    perf_test_bulk, EventRecorderBulkTest,
    testing::Combine(
        testing::Values(1, 2, 4),
        testing::Values(16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192)));
#else
INSTANTIATE_TEST_SUITE_P(
    perf_test_bulk, EventRecorderBulkTest,
    testing::Combine(testing::Values(4), testing::Values(128)));
#endif
