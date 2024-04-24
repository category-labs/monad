#include "test_fixture.hpp"

#include <monad/async/boost_fiber_wrappers.hpp>
#include <monad/async/concepts.hpp>
#include <monad/async/config.hpp>
#include <monad/async/storage_pool.hpp>
#include <monad/core/assert.h>

#include <boost/fiber/future/async.hpp>
#include <boost/fiber/future/future.hpp>
#include <boost/fiber/future/future_status.hpp>
#include <boost/fiber/operations.hpp>
#include <boost/lockfree/policies.hpp>
#include <boost/lockfree/queue.hpp>
#include <boost/outcome/try.hpp>

#include <atomic>
#include <chrono>
#include <cstddef>
#include <cstring>
#include <iostream>
#include <ostream>
#include <stop_token>
#include <thread>
#include <vector>

#include <sched.h>
#include <unistd.h>

using namespace MONAD_ASYNC_NAMESPACE;

struct BoostFiberWrappers
    : public monad::test::AsyncTestFixture<::testing::Test>
{
};

TEST_F(BoostFiberWrappers, fiber_read)
{
    auto impl = [&]() -> result<std::vector<std::byte>> {
        // This initiates the i/o reading DISK_PAGE_SIZE bytes from offset
        // 0, returning a boost fiber future like object
        auto fut = boost_fibers::read_single_buffer(
            *shared_state_()->testio, chunk_offset_t{0, 0}, DISK_PAGE_SIZE);
        // You can do other stuff here, like initiate more i/o or do compute

        // When you really do need the result to progress further, suspend
        // execution until the i/o completes. The TRY operation will
        // propagate any failures out the return type of this lambda, if the
        // operation was successful `res` get the result.
        BOOST_OUTCOME_TRY(auto bytesread_, fut.get());
        auto &bytesread = bytesread_.get();

        // Return a copy of the registered buffer with lifetime held by fut
        return std::vector<std::byte>(bytesread.begin(), bytesread.end());
    };

    // Launch the fiber task
    ::boost::fibers::future<result<std::vector<std::byte>>> fut =
        ::boost::fibers::async(impl);
    // Pump the loop until the fiber completes
    while (::boost::fibers::future_status::ready !=
           fut.wait_for(std::chrono::seconds(0))) {
        shared_state_()->testio->poll_blocking(1);
    }
    // Get the result of the fiber task
    result<std::vector<std::byte>> res = fut.get();
    // The result may contain a failure
    if (!res) {
        std::cerr << "ERROR: " << res.error().message().c_str() << std::endl;
        ASSERT_TRUE(res);
    }
    // If successful, did it read the right data?
    EXPECT_EQ(DISK_PAGE_SIZE, res.value().size());
    EXPECT_EQ(
        0,
        memcmp(
            res.value().data(),
            shared_state_()->testfilecontents.data(),
            DISK_PAGE_SIZE));
}

TEST_F(BoostFiberWrappers, fiber_timeout)
{
    auto impl = [&]() -> std::chrono::steady_clock::duration {
        auto begin = std::chrono::steady_clock::now();
        boost_fibers::timed_delay(
            *shared_state_()->testio, std::chrono::seconds(1))
            .get()
            .value();
        return std::chrono::steady_clock::now() - begin;
    };
    ::boost::fibers::future<std::chrono::steady_clock::duration> fut =
        ::boost::fibers::async(impl);
    while (::boost::fibers::future_status::ready !=
           fut.wait_for(std::chrono::seconds(0))) {
        shared_state_()->testio->poll_blocking(1);
    }
    std::chrono::steady_clock::duration const res = fut.get();
    EXPECT_GE(res, std::chrono::seconds(1));
}

TEST_F(BoostFiberWrappers, resume_execution_upon)
{
    std::atomic<AsyncIO *> other{nullptr};
    std::jthread thr([&](std::stop_token token) {
        storage_pool pool{use_anonymous_inode_tag{}};
        auto ring = shared_state_()->make_ring();
        auto buf = shared_state_()->make_buffers(ring);
        AsyncIO io(pool, buf);
        other = &io;
        while (!token.stop_requested()) {
            ::boost::this_fiber::yield();
            io.poll_nonblocking(1);
        }
        io.wait_until_done();
    });
    while (other == nullptr) {
        std::this_thread::yield();
    }
    static ::boost::lockfree::queue<pid_t, ::boost::lockfree::capacity<4>>
        thread_ids;
    std::atomic<bool> done{false};
    auto impl = [&] {
        const pid_t original_tid = gettid();
        MONAD_ASSERT(thread_ids.push(original_tid));
        boost_fibers::resume_execution_upon(*other).get().value();
        const pid_t new_tid = gettid();
        MONAD_ASSERT(thread_ids.push(new_tid));
        // Can't complete on a thread different to original, it would be a
        // race.
        boost_fibers::resume_execution_upon(*shared_state_()->testio)
            .get()
            .value();
        const pid_t final_tid = gettid();
        MONAD_ASSERT(thread_ids.push(final_tid));
        done = true;
    };
    ::boost::fibers::future<void> fut = ::boost::fibers::async(impl);
    while (!done) {
        ::boost::this_fiber::yield();
        shared_state_()->testio->poll_nonblocking(1);
    }
    thr.request_stop();
    thr.join();
    fut.get();
    std::vector<pid_t> tids;
    while (!thread_ids.empty()) {
        pid_t v;
        if (thread_ids.pop(v)) {
            tids.push_back(v);
            std::cout << "\n   " << v;
        }
    }
    std::cout << std::endl;
    ASSERT_EQ(tids.size(), 3);
    EXPECT_EQ(tids[0], gettid());
    EXPECT_NE(tids[1], gettid());
    EXPECT_EQ(tids[2], gettid());
}
