#include <atomic>
#include <bit>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <format>
#include <latch>
#include <span>
#include <thread>
#include <tuple>
#include <vector>

#include <pthread.h>
#include <sched.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <unistd.h>

#include <gtest/gtest.h>
#include <monad/core/likely.h>
#include <monad/event/event_iterator.h>
#include <monad/event/event_recorder.h>
#include <monad/event/event_ring.h>

constexpr uint64_t MaxPerfIterations = 1UL << 20;

// Running the tests with the reader disabled is a good measure of how
// expensive the multithreaded lock-free recording in the writer is, without
// any potential synchronization effects of a reader.
constexpr bool ENABLE_READER = true;

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

// Event type code
constexpr uint16_t TEST_COUNTER = 1;

// Payload of the TEST_COUNTER event type
struct test_counter_payload
{
    uint8_t writer_id;
    uint64_t counter;
};

// A writer thread records TEST_COUNTER events as fast as possible, then prints
// its average recording speed (in ns/event). Because of all the atomic
// synchronization in the event ring control structure, writing time increases
// as more concurrent writing threads are used. Accordingly, we divide
// MaxPerfIterations by the number of writers, so that the test doesn't take
// too long.
static void writer_main(
    monad_event_recorder *recorder, std::latch *latch, uint8_t writer_id,
    uint8_t writer_thread_count, uint32_t payload_size)
{
    using std::chrono::duration_cast, std::chrono::nanoseconds;
    std::byte payload_buf[1 << 14]{};

    uint64_t const writer_iterations = MaxPerfIterations / writer_thread_count;
    auto *const test_counter =
        std::bit_cast<test_counter_payload *>(&payload_buf[0]);
    test_counter->writer_id = writer_id;
    latch->arrive_and_wait();
    sleep(1);
    auto const start_time = std::chrono::system_clock::now();
    for (uint64_t counter = 0; counter < writer_iterations; ++counter) {
        test_counter->counter = counter;
        monad_event_record(recorder, TEST_COUNTER, payload_buf, payload_size);
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

// The reader thread reads events and does some basic validation of them (e.g.,
// that the sequence numbers are in order, that their payload size is correct,
// etc.)
[[maybe_unused]] static void reader_main(
    struct monad_event_ring const *event_ring, std::latch *latch,
    uint8_t writer_thread_count, uint32_t expected_len)
{
    uint64_t const max_writer_iteration =
        MaxPerfIterations / writer_thread_count;
    alignas(64) monad_event_iterator iter;
    std::vector<uint64_t> expected_counters;
    expected_counters.resize(writer_thread_count, 0);
    ASSERT_EQ(0, monad_event_ring_init_iterator(event_ring, &iter));

    latch->arrive_and_wait();
    // Regardless of where the most recent event is, start from zero
    uint64_t last_seqno = iter.read_last_seqno = 0;
    while (last_seqno < max_writer_iteration) {
        monad_event_descriptor event;
        monad_event_next_result const nr =
            monad_event_iterator_try_next(&iter, &event);
        if (MONAD_UNLIKELY(nr == MONAD_EVENT_NOT_READY)) {
            __builtin_ia32_pause();
            continue;
        }
        ASSERT_EQ(MONAD_EVENT_SUCCESS, nr);
        EXPECT_EQ(last_seqno + 1, event.seqno);
        last_seqno = event.seqno;

        ASSERT_EQ(TEST_COUNTER, event.event_type);
        ASSERT_EQ(event.payload_size, expected_len);
        auto const test_counter = *static_cast<test_counter_payload const *>(
            monad_event_payload_peek(&iter, &event));
        ASSERT_TRUE(monad_event_payload_check(&iter, &event));
        ASSERT_GT(writer_thread_count, test_counter.writer_id);
        EXPECT_EQ(
            expected_counters[test_counter.writer_id], test_counter.counter);
        expected_counters[test_counter.writer_id] = test_counter.counter + 1;
    }
}

class EventRecorderBulkTest
    : public testing::TestWithParam<std::tuple<uint8_t, uint32_t>>
{
protected:
    void SetUp() override
    {
        constexpr char TEST_MEMFD_NAME[] = "memfd:event_recorder_test";
        constexpr uint8_t DESCRIPTORS_SHIFT = 20;
        constexpr uint8_t PAYLOAD_BUF_SHIFT = 28;
        int const ring_fd =
            memfd_create(TEST_MEMFD_NAME, MFD_CLOEXEC | MFD_HUGETLB);

        monad_event_ring_size ring_size;
        ASSERT_EQ(
            0,
            monad_event_ring_init_size(
                DESCRIPTORS_SHIFT, PAYLOAD_BUF_SHIFT, &ring_size));
        ASSERT_EQ(
            0,
            ftruncate(
                ring_fd,
                static_cast<off_t>(monad_event_ring_calc_storage(&ring_size))));
        ASSERT_EQ(
            0,
            monad_event_ring_init_file(
                &ring_size, ring_fd, 0, TEST_MEMFD_NAME));

        ASSERT_EQ(
            0,
            monad_event_ring_mmap(
                &event_ring_,
                PROT_READ | PROT_WRITE,
                MAP_POPULATE | MAP_HUGETLB,
                ring_fd,
                0,
                TEST_MEMFD_NAME));
        (void)close(ring_fd);
    }

    void TearDown() override
    {
        monad_event_ring_unmap(&event_ring_);
    }

    monad_event_ring event_ring_ = {};
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

    // The current recorder implementation is multi-threaded so we only need
    // one of these, to be shared with all writer threads
    alignas(64) monad_event_recorder recorder;
    ASSERT_EQ(0, monad_event_ring_init_recorder(&event_ring_, &recorder));
    for (uint8_t t = 0; t < writer_thread_count; ++t) {
        char name[16];
        snprintf(name, sizeof name, "writer-%hhu", t);
        ASSERT_TRUE(alloc_cpu(&avail_cpus, &thr_cpu));
        auto &thread = writer_threads.emplace_back(
            writer_main,
            &recorder,
            &sync_latch,
            t,
            writer_thread_count,
            payload_size);
        auto const thr = thread.native_handle();
        pthread_setname_np(thr, name);
        ASSERT_EQ(0, pthread_setaffinity_np(thr, sizeof thr_cpu, &thr_cpu));
    }
    std::thread reader_thread;

    if constexpr (ENABLE_READER) {
        ASSERT_TRUE(alloc_cpu(&avail_cpus, &thr_cpu));
        reader_thread = std::thread{
            reader_main,
            &event_ring_,
            &sync_latch,
            writer_thread_count,
            payload_size};
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

// Running the full test every time is too slow so we usually leave the
// `RUN_FULL_EVENT_RECORDER_TEST` macro undefined. If you manually define this
// to 1 (and ideally increase MaxPerfIterations so that it's less noisy) you
// will get recorder performance micro-benchmarks for different combinations
// of concurrent threads and payload sizes.

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
