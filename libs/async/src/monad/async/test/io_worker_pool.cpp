#include "test_fixture.hpp"

#include <monad/async/concepts.hpp>
#include <monad/async/config.hpp>
#include <monad/async/connected_operation.hpp>
#include <monad/async/erased_connected_operation.hpp>
#include <monad/async/io_senders.hpp>
#include <monad/async/io_worker_pool.hpp>
#include <monad/async/sender_errc.hpp>
#include <monad/async/util.hpp>
#include <monad/core/array.hpp>
#include <monad/core/assert.h>
#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <boost/lockfree/policies.hpp>
#include <boost/lockfree/queue.hpp>

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstddef>
#include <cstring>
#include <deque>
#include <iostream>
#include <memory>
#include <ostream>
#include <thread>
#include <utility>
#include <vector>

#include <sched.h>
#include <unistd.h>

struct AsyncReadIoWorkerPool
    : public monad::test::AsyncTestFixture<::testing::Test>
{
};

TEST_F(AsyncReadIoWorkerPool, construct_dynamic)
{
    MONAD_ASYNC_NAMESPACE::AsyncReadIoWorkerPool const workerpool(
        *shared_state_()->testio,
        MAX_CONCURRENCY,
        shared_state_()->make_ring,
        shared_state_()->make_buffers);
}

template <class... Args>
struct TypeList;

TEST_F(AsyncReadIoWorkerPool, construct_fixed)
{
    // boost::lockfree::capacity causes overalignment
    delete new auto(MONAD_ASYNC_NAMESPACE::AsyncReadIoWorkerPool<
                    TypeList<::boost::lockfree::capacity<16>>>(
        *shared_state_()->testio,
        MAX_CONCURRENCY,
        shared_state_()->make_ring,
        shared_state_()->make_buffers));
}

TEST_F(AsyncReadIoWorkerPool, works)
{
    using namespace MONAD_ASYNC_NAMESPACE;
    MONAD_ASYNC_NAMESPACE::AsyncReadIoWorkerPool workerpool(
        *shared_state_()->testio,
        MAX_CONCURRENCY,
        shared_state_()->make_ring,
        shared_state_()->make_buffers);
    static ::boost::lockfree::
        queue<pid_t, ::boost::lockfree::capacity<MAX_CONCURRENCY * 2>>
            thread_ids;
    static std::atomic<int> count(0);

    struct sender_t
    {
        using result_type = result<void>;

        result_type operator()(erased_connected_operation *) noexcept
        {
            MONAD_ASSERT(thread_ids.push(gettid()));
            count += 1;
            while (count > 0) {
                std::this_thread::yield();
            }
            count -= 1;
            return sender_errc::initiation_immediately_completed;
        }
    };

    static_assert(sender<sender_t>);

    struct receiver_t
    {
        void set_value(erased_connected_operation *, result<void> res)
        {
            MONAD_ASSERT(res);
            MONAD_ASSERT(thread_ids.push(gettid()));
        }
    };

    static_assert(receiver<receiver_t>);
    using connected_type = decltype(connect(
        *shared_state_()->testio,
        execute_on_worker_pool<sender_t>{},
        receiver_t{}));
    auto states = ::monad::make_array<connected_type, MAX_CONCURRENCY>(
        std::piecewise_construct,
        execute_on_worker_pool<sender_t>{workerpool},
        receiver_t{});
    EXPECT_EQ(shared_state_()->testio->io_in_flight(), 0);
    EXPECT_TRUE(workerpool.currently_idle());
    for (auto &i : states) {
        i.initiate();
    }
    while (count < int(MAX_CONCURRENCY)) {
        std::this_thread::yield();
    }
    EXPECT_FALSE(workerpool.currently_idle());
    EXPECT_GE(workerpool.busy_estimate(), 0.99);
    EXPECT_EQ(shared_state_()->testio->io_in_flight(), 0);
    count = 0;
    while (count > -int(MAX_CONCURRENCY)) {
        std::this_thread::yield();
    }
    std::vector<pid_t> tids;
    std::cout << "   Master AsyncIO thread id is " << gettid();
    while (tids.size() < MAX_CONCURRENCY * 2) {
        shared_state_()->testio->wait_until_done();
        pid_t v = 0;
        if (thread_ids.pop(v)) {
            tids.push_back(v);
            std::cout << "\n   " << v;
        }
        std::this_thread::yield();
    }
    std::cout << std::endl;
    // The first MAX_CONCURRENCY must be dissimilar, the last
    // MAX_CONCURRENCY must be our tid
    for (size_t n = 0; n < MAX_CONCURRENCY; n++) {
        EXPECT_EQ(std::count(tids.begin(), tids.end(), tids[n]), 1);
    }
    for (size_t n = MAX_CONCURRENCY; n < MAX_CONCURRENCY * 2; n++) {
        EXPECT_EQ(tids[n], gettid());
    }
}

TEST_F(AsyncReadIoWorkerPool, workers_can_reinitiate)
{
    using namespace MONAD_ASYNC_NAMESPACE;
    MONAD_ASYNC_NAMESPACE::AsyncReadIoWorkerPool workerpool(
        *shared_state_()->testio,
        MAX_CONCURRENCY,
        shared_state_()->make_ring,
        shared_state_()->make_buffers);
    static ::boost::lockfree::
        queue<pid_t, ::boost::lockfree::capacity<MAX_CONCURRENCY * 2>>
            thread_ids;
    static std::atomic<int> count(MAX_CONCURRENCY);

    struct sender_t
    {
        using result_type = result<void>;

        result_type operator()(erased_connected_operation *) noexcept
        {
            MONAD_ASSERT(thread_ids.push(gettid()));
            return (count.fetch_sub(1) == 1)
                       ? sender_errc::initiation_immediately_completed
                       : sender_errc::operation_must_be_reinitiated;
        }
    };

    static_assert(sender<sender_t>);

    struct receiver_t
    {
        bool done{false};

        void set_value(erased_connected_operation *, result<void> res)
        {
            MONAD_ASSERT(res);
            done = true;
        }
    };

    static_assert(receiver<receiver_t>);
    auto state = connect(
        *shared_state_()->testio,
        execute_on_worker_pool<sender_t>{workerpool},
        receiver_t{});
    state.initiate();
    std::vector<pid_t> tids;
    std::cout << "   Master AsyncIO thread id is " << gettid();
    while (tids.size() < MAX_CONCURRENCY) {
        shared_state_()->testio->wait_until_done();
        pid_t v = 0;
        if (thread_ids.pop(v)) {
            tids.push_back(v);
            std::cout << "\n   " << v;
        }
        std::this_thread::yield();
    }
    std::cout << std::endl;
    while (!state.receiver().done) {
        shared_state_()->testio->wait_until_done();
    }
}

TEST_F(AsyncReadIoWorkerPool, workers_can_initiate_new_work)
{
    using namespace MONAD_ASYNC_NAMESPACE;
    static auto workerpool_ =
        std::make_unique<MONAD_ASYNC_NAMESPACE::AsyncReadIoWorkerPool<>>(
            *shared_state_()->testio,
            MAX_CONCURRENCY,
            shared_state_()->make_ring,
            shared_state_()->make_buffers);
    static auto &workerpool = *workerpool_;
    static ::boost::lockfree::queue<pid_t> thread_ids(8);
    static std::atomic<int> count(MAX_CONCURRENCY);

    struct sender2_t
    {
        using result_type = result<void>;
        pid_t mytid{0};

        result_type operator()(erased_connected_operation *) noexcept
        {
            mytid = gettid();
            MONAD_ASSERT(thread_ids.push(gettid()));
            return sender_errc::initiation_immediately_completed;
        }
    };

    static_assert(sender<sender2_t>);

    struct receiver2_t
    {
        erased_connected_operation *original_io_state{nullptr};
        sender2_t *sender{nullptr};

        explicit receiver2_t(erased_connected_operation *original_io_state_)
            : original_io_state(original_io_state_)
        {
        }

        void set_value(erased_connected_operation *, result<void> res)
        {
            MONAD_ASSERT(res);
            // Receivers must execute where the operation was constructed
            MONAD_ASSERT(sender->mytid == gettid());
            if (count.fetch_sub(1) == 1) {
                original_io_state->completed(success());
            }
        }
    };

    static_assert(receiver<receiver2_t>);

    struct sender1_t
    {
        using result_type = result<void>;
        using connected_state_type = decltype(connect(
            *shared_state_()->testio,
            execute_on_worker_pool<sender2_t>{workerpool},
            receiver2_t{std::declval<erased_connected_operation *>()}));
        std::unique_ptr<connected_state_type> states[MAX_CONCURRENCY];

        result_type operator()(erased_connected_operation *st) noexcept
        {
            MONAD_ASSERT(thread_ids.push(gettid()));
            for (auto &state : states) {
                state = std::unique_ptr<connected_state_type>( // NOLINT
                    new connected_state_type(connect( // NOLINT
                        *st->executor(),
                        execute_on_worker_pool<sender2_t>{workerpool},
                        receiver2_t{st})));
                state->receiver().sender = &state->sender();
            }
            for (auto &state : states) {
                state->initiate();
            }
            return success();
        }
    };

    static_assert(sender<sender1_t>);

    struct receiver1_t
    {
        void set_value(erased_connected_operation *, result<void> res)
        {
            MONAD_ASSERT(res);
            MONAD_ASSERT(thread_ids.push(gettid()));
        }
    };

    auto state = connect(
        *shared_state_()->testio,
        execute_on_worker_pool<sender1_t>{workerpool},
        receiver1_t{});
    state.initiate();
    std::vector<pid_t> tids;
    std::cout << "   Master AsyncIO thread id is " << gettid();
    while (tids.size() < MAX_CONCURRENCY + 2) {
        shared_state_()->testio->wait_until_done();
        pid_t v = 0;
        if (thread_ids.pop(v)) {
            tids.push_back(v);
            std::cout << "\n   " << v;
        }
        std::this_thread::yield();
    }
    std::cout << std::endl;
    EXPECT_EQ(tids.back(), gettid());
    workerpool_.reset();
}

TEST_F(AsyncReadIoWorkerPool, workers_can_do_read_io)
{
    using namespace MONAD_ASYNC_NAMESPACE;
    MONAD_ASYNC_NAMESPACE::AsyncReadIoWorkerPool workerpool(
        *shared_state_()->testio,
        MAX_CONCURRENCY,
        shared_state_()->make_ring,
        shared_state_()->make_buffers);

    struct sender_t
    {
        using result_type = result<void>;

        chunk_offset_t const offset;

        struct receiver_t
        {
            chunk_offset_t const offset;
            erased_connected_operation *const original_io_state;

            void set_value(
                erased_connected_operation *,
                monad::async::read_single_buffer_sender::result_type res)
            {
                if (!res) {
                    std::cerr << res.assume_error().message().c_str()
                              << std::endl;
                }
                MONAD_ASSERT(res);
                MONAD_ASSERT(
                    0 == memcmp(
                             res.assume_value().get().data(),
                             shared_state_()->testfilecontents.data() +
                                 offset.offset,
                             DISK_PAGE_SIZE));
                original_io_state->completed(success());
            }
        };

        explicit sender_t(chunk_offset_t offset_)
            : offset(offset_)
        {
        }

        result_type operator()(erased_connected_operation *io_state) noexcept
        {
            auto state =
                io_state->executor()
                    ->make_connected<read_single_buffer_sender, receiver_t>(
                        read_single_buffer_sender{offset, DISK_PAGE_SIZE},
                        receiver_t{offset, io_state});
            state->initiate();
            state.release();
            return success();
        }
    };

    static_assert(sender<sender_t>);

    struct receiver_t
    {
        bool done{false};

        void set_value(erased_connected_operation *, result<void> res)
        {
            MONAD_ASSERT(res);
            done = true;
        }
    };

    using state_type = decltype(connect(
        *shared_state_()->testio,
        execute_on_worker_pool<sender_t>{workerpool, chunk_offset_t{0, 0}},
        receiver_t{}));
    std::deque<std::unique_ptr<state_type>> states;
    for (size_t n = 0; n < 100; n++) {
        chunk_offset_t const offset(
            0,
            round_down_align<DISK_PAGE_BITS>(
                shared_state_()->test_rand() % TEST_FILE_SIZE));
        states.emplace_back(new state_type(
            execute_on_worker_pool<sender_t>{workerpool, offset},
            receiver_t{}));
        states.back()->initiate();
        while (states.size() >= MAX_CONCURRENCY) {
            shared_state_()->testio->wait_until_done();
            if (states.front()->receiver().done) {
                states.pop_front();
            }
        }
    }
    while (!states.empty()) {
        shared_state_()->testio->wait_until_done();
        if (states.front()->receiver().done) {
            states.pop_front();
        }
    }
}

TEST_F(AsyncReadIoWorkerPool, async_completions_are_not_racy)
{
    using namespace MONAD_ASYNC_NAMESPACE;
    MONAD_ASYNC_NAMESPACE::AsyncReadIoWorkerPool workerpool(
        *shared_state_()->testio,
        MAX_CONCURRENCY,
        shared_state_()->make_ring,
        shared_state_()->make_buffers);

    struct sender_t
    {
        bool defers{false};
        using result_type = result<void>;

        result_type operator()(erased_connected_operation *io_state) noexcept
        {
            // This needs to defer until this exits, otherwise
            // there is a race condition
            io_state->completed(success());
            std::this_thread::sleep_for(std::chrono::seconds(1));
            defers = true;
            return success();
        }
    };

    static_assert(sender<sender_t>);

    struct receiver_t
    {
        bool done{false};

        void set_value(erased_connected_operation *, result<void>)
        {
            done = true;
        }
    };

    static_assert(receiver<receiver_t>);
    auto state = connect(
        *shared_state_()->testio,
        execute_on_worker_pool<sender_t>{workerpool},
        receiver_t{});
    ASSERT_FALSE(state.sender().defers);
    state.initiate();
    while (!state.receiver().done) {
        shared_state_()->testio->wait_until_done();
    }
    EXPECT_TRUE(state.sender().defers);
}
