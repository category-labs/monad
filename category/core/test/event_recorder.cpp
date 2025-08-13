// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <bit>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <latch>
#include <print>
#include <thread>
#include <tuple>
#include <vector>

#include <fcntl.h>
#include <pthread.h>
#include <sched.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <unistd.h>

#include <category/core/event/event_iterator.h>
#include <category/core/event/event_recorder.h>
#include <category/core/event/event_ring.h>
#include <category/core/event/event_ring_util.h>
#include <category/core/event/test_event_ctypes.h>
#include <category/core/likely.h>

#include <gtest/gtest.h>

static uint8_t PERF_ITER_SHIFT = 20;

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

// A writer thread records TEST_COUNTER events as fast as possible, then prints
// its average recording speed (in ns/event). Because of all the atomic
// synchronization in the event ring control structure, writing time increases
// as more concurrent writing threads are used. Accordingly, we divide the
// total number of iterations by the number of writers, so that the test doesn't
// take too long.
static void writer_main(
    monad_event_recorder *recorder, std::latch *latch, uint8_t writer_id,
    uint8_t writer_thread_count, uint32_t payload_size)
{
    using std::chrono::duration_cast, std::chrono::nanoseconds;
    std::byte local_payload_buf[1 << 14]{};

    uint64_t const writer_iterations =
        (1UL << PERF_ITER_SHIFT) / writer_thread_count;
    auto *const test_counter =
        std::bit_cast<monad_test_event_counter *>(&local_payload_buf[0]);
    test_counter->writer_id = writer_id;
    latch->arrive_and_wait();
    sleep(1);
    auto const start_time = std::chrono::system_clock::now();
    for (uint64_t counter = 0; counter < writer_iterations; ++counter) {
        test_counter->counter = counter;

        uint64_t seqno;
        uint8_t *ring_payload_buf;

        monad_event_descriptor *const event = monad_event_recorder_reserve(
            recorder, payload_size, &seqno, &ring_payload_buf);
        event->event_type = MONAD_TEST_EVENT_COUNTER;
        memcpy(ring_payload_buf, local_payload_buf, payload_size);
        monad_event_recorder_commit(event, seqno);
    }
    auto const end_time = std::chrono::system_clock::now();
    auto const elapsed_nanos = static_cast<uint64_t>(
        duration_cast<nanoseconds>(end_time - start_time).count());
    std::println(
        stdout,
        "writer {} recording speed: {} ns/evt of payload size {} "
        "[{} iterations in {}]",
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
    monad_event_ring const *event_ring, std::latch *latch,
    uint8_t writer_thread_count, uint32_t expected_len)
{
    uint64_t const max_writer_iteration =
        (1UL << PERF_ITER_SHIFT) / writer_thread_count;
    alignas(64) monad_event_iterator iter;
    std::vector<uint64_t> expected_counters;
    expected_counters.resize(writer_thread_count, 0);
    ASSERT_EQ(0, monad_event_ring_init_iterator(event_ring, &iter));

    latch->arrive_and_wait();
    // Regardless of where the most recent event is, start from zero
    uint64_t last_seqno = iter.read_last_seqno = 0;
    while (last_seqno < max_writer_iteration) {
        monad_event_descriptor event;
        monad_event_iter_result const ir =
            monad_event_iterator_try_next(&iter, &event);
        if (MONAD_UNLIKELY(ir == MONAD_EVENT_NOT_READY)) {
            __builtin_ia32_pause();
            continue;
        }
        ASSERT_EQ(MONAD_EVENT_SUCCESS, ir);
        EXPECT_EQ(last_seqno + 1, event.seqno);
        last_seqno = event.seqno;

        ASSERT_EQ(MONAD_TEST_EVENT_COUNTER, event.event_type);
        ASSERT_EQ(event.payload_size, expected_len);
        auto const test_counter =
            *static_cast<monad_test_event_counter const *>(
                monad_event_ring_payload_peek(event_ring, &event));
        ASSERT_TRUE(monad_event_ring_payload_check(event_ring, &event));
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
        constexpr uint8_t DESCRIPTORS_SHIFT = 20;
        constexpr uint8_t PAYLOAD_BUF_SHIFT = 28;

        int ring_fd;
        char const *error_name;
        int mmap_extra_flags = MAP_POPULATE;

        if (char const *f = std::getenv("EVENT_RECORDER_FILE")) {
            // When given an explicit file for an event ring via an environment
            // variable, use that instead of memfd_create
            constexpr mode_t FS_MODE =
                S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH;

            // If the environment defines EVENT_RECORDER_FILE without a value,
            // use the default value
            fs_path_ =
                strcmp(f, "") == 0 ? MONAD_EVENT_DEFAULT_TEST_RING_PATH : f;

            ring_fd =
                open(fs_path_.c_str(), O_RDWR | O_CREAT | O_TRUNC, FS_MODE);
            ASSERT_NE(-1, ring_fd);
            error_name = fs_path_.c_str();

            // Use MAP_HUGETLB only if the file is on a filesystem that
            // supports it
            bool fs_supports_hugetlb;
            ASSERT_EQ(
                0,
                monad_check_path_supports_map_hugetlb(
                    fs_path_.c_str(), &fs_supports_hugetlb));
            mmap_extra_flags |= fs_supports_hugetlb ? MAP_HUGETLB : 0;
        }
        else {
            // EVENT_RECORDER_FILE is not defined in the environment;
            // use memfd_create
            constexpr char TEST_MEM_FD_NAME[] = "memfd:event_recorder_test";
            ring_fd = memfd_create(TEST_MEM_FD_NAME, MFD_CLOEXEC | MFD_HUGETLB);
            ASSERT_NE(-1, ring_fd);
            error_name = TEST_MEM_FD_NAME;
            mmap_extra_flags |= MAP_HUGETLB;
        }

        monad_event_ring_simple_config const ring_config = {
            .descriptors_shift = DESCRIPTORS_SHIFT,
            .payload_buf_shift = PAYLOAD_BUF_SHIFT,
            .context_large_pages = 0,
            .content_type = MONAD_EVENT_CONTENT_TYPE_TEST,
            .schema_hash = g_monad_test_event_schema_hash};
        ASSERT_EQ(
            0,
            monad_event_ring_init_simple(&ring_config, ring_fd, 0, error_name));
        ASSERT_EQ(
            0,
            monad_event_ring_mmap(
                &event_ring_,
                PROT_READ | PROT_WRITE,
                mmap_extra_flags,
                ring_fd,
                0,
                error_name));
        (void)close(ring_fd);

        if (char const *s = std::getenv("EVENT_RECORDER_ITER_SHIFT")) {
            char *end;
            unsigned long const u = strtoul(s, &end, 0);
            ASSERT_EQ('\0', *end);
            ASSERT_LT(u, 50);
            PERF_ITER_SHIFT = static_cast<uint8_t>(u);
        }
    }

    void TearDown() override
    {
        monad_event_ring_unmap(&event_ring_);
        if (!empty(fs_path_)) {
            (void)unlink(fs_path_.c_str());
            fs_path_.clear();
        }
    }

    monad_event_ring event_ring_ = {};
    std::string fs_path_;
};

TEST_P(EventRecorderBulkTest, )
{
    auto const [writer_thread_count, payload_size] = GetParam();
    std::latch sync_latch{writer_thread_count + (ENABLE_READER ? 2 : 1)};
    std::vector<std::thread> writer_threads;
    cpu_set_t avail_cpus;
    cpu_set_t thr_cpu;

    ASSERT_EQ(
        0,
        pthread_getaffinity_np(pthread_self(), sizeof avail_cpus, &avail_cpus));

    // The current recorder implementation is multi-threaded so we only need
    // one of these, to be shared with all writer threads
    alignas(64) monad_event_recorder recorder;
    ASSERT_EQ(0, monad_event_ring_init_recorder(&event_ring_, &recorder));
    for (uint8_t t = 0; t < writer_thread_count; ++t) {
        char name[16];
        *std::format_to(name, "writer-{}", t) = '\0';
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
// to 1 (and ideally increase PERF_ITER_SHIFT so that it's less noisy) you
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
