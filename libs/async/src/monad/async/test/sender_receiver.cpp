#if defined(__GNUC__) && !defined(__clang__)
    #pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
#endif

#include "test_fixture.hpp"

#include <monad/async/concepts.hpp>
#include <monad/async/config.hpp>
#include <monad/async/connected_operation.hpp>
#include <monad/async/detail/scope_polyfill.hpp>
#include <monad/async/erased_connected_operation.hpp>
#include <monad/async/io.hpp>
#include <monad/async/io_senders.hpp>
#include <monad/async/sender_errc.hpp>
#include <monad/async/storage_pool.hpp>
#include <monad/async/util.hpp>
#include <monad/core/array.hpp>
#include <monad/core/assert.h>
#include <monad/core/small_prng.hpp>
#include <monad/io/buffers.hpp>
#include <monad/io/ring.hpp>

#include <boost/fiber/fiber.hpp>
#ifdef __clang__
    #pragma clang diagnostic push
    #pragma clang diagnostic ignored "-Wdeprecated-declarations"
#endif
#include <boost/fiber/future.hpp>
#ifdef __clang__
    #pragma clang diagnostic pop
#endif
#include <boost/fiber/future/promise.hpp>
#include <boost/fiber/operations.hpp>
#include <boost/outcome/config.hpp>
#include <boost/outcome/coroutine_support.hpp>

#include <array>
#include <atomic>
#include <cassert>
#include <chrono>
#include <coroutine>
#include <cstddef>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <future>
#include <iostream>
#include <memory>
#include <optional>
#include <ostream>
#include <thread>
#include <tuple>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct AsyncIO : public monad::test::AsyncTestFixture<::testing::Test>
{
};

struct read_single_buffer_operation_states_base_
{
    virtual bool reinitiate(
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *i,
        MONAD_ASYNC_NAMESPACE::read_single_buffer_sender::buffer_type
            buffer) = 0;
};

template <MONAD_ASYNC_NAMESPACE::receiver Receiver>
class read_single_buffer_operation_states_ final
    : public read_single_buffer_operation_states_base_
{
    using io_state_type_ =
        MONAD_ASYNC_NAMESPACE::AsyncIO::connected_operation_unique_ptr_type<
            MONAD_ASYNC_NAMESPACE::read_single_buffer_sender, Receiver>;
    typename AsyncIO::shared_state_t *const fixture_shared_state_;
    std::vector<io_state_type_> states_;
    bool test_is_done_{false};
    unsigned op_count_{0};

public:
    template <class... Args>
    explicit read_single_buffer_operation_states_(
        typename AsyncIO::shared_state_t *fixture_shared_state, size_t total,
        Args &&...args)
        : fixture_shared_state_(fixture_shared_state)
    {
        using namespace MONAD_ASYNC_NAMESPACE;
        states_.reserve(total);
        for (size_t n = 0; n < total; n++) {
            chunk_offset_t const offset(
                0,
                round_down_align<DISK_PAGE_BITS>(
                    fixture_shared_state_->test_rand() %
                    (::AsyncIO::TEST_FILE_SIZE - DISK_PAGE_SIZE)));
            states_.push_back(fixture_shared_state_->testio->make_connected(
                read_single_buffer_sender(offset, DISK_PAGE_SIZE),
                Receiver{this, std::forward<Args>(args)...}));
        }
    }

    ~read_single_buffer_operation_states_()
    {
        stop();
    }

    unsigned count() const noexcept
    {
        return op_count_;
    }

    void initiate()
    {
        test_is_done_ = false;
        for (auto &i : states_) {
            i->initiate();
        }
        op_count_ = static_cast<unsigned int>(states_.size());
    }

    void stop()
    {
        test_is_done_ = true;
        fixture_shared_state_->testio->wait_until_done();
    }

    virtual bool reinitiate(
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *i,
        MONAD_ASYNC_NAMESPACE::read_single_buffer_sender::buffer_type buffer)
        override final
    {
        using namespace MONAD_ASYNC_NAMESPACE;
        auto *state = static_cast<typename io_state_type_::pointer>(i);
        EXPECT_EQ(
            buffer.front(),
            fixture_shared_state_
                ->testfilecontents[state->sender().offset().offset]);
        if (!test_is_done_) {
            chunk_offset_t const offset(
                0,
                round_down_align<DISK_PAGE_BITS>(
                    fixture_shared_state_->test_rand() %
                    (::AsyncIO::TEST_FILE_SIZE - DISK_PAGE_SIZE)));
            state->reset(std::tuple{offset, DISK_PAGE_SIZE}, std::tuple{});
            state->initiate();
            op_count_++;
            return true;
        }
        return false;
    }

    MONAD_ASYNC_NAMESPACE::read_single_buffer_sender &
    sender(size_t idx) noexcept
    {
        return states_[idx]->sender();
    }

    Receiver &receiver(size_t idx) noexcept
    {
        return states_[idx]->receiver();
    }
};

TEST_F(AsyncIO, timed_delay_sender_receiver)
{
    using namespace MONAD_ASYNC_NAMESPACE;
    auto check = [&](char const *desc, auto &&get_now, auto timeout) {
        struct receiver_t
        {
            bool done{false};
            void set_value(erased_connected_operation *, result<void> res)
            {
                ASSERT_TRUE(res);
                done = true;
            }
        };
        auto state = connect(
            *shared_state_()->testio,
            timed_delay_sender(timeout),
            receiver_t{});
        std::cout << "   " << desc << " ..." << std::endl;
        auto begin = get_now();
        state.initiate();
        while (!state.receiver().done) {
            shared_state_()->testio->poll_blocking(1);
        }
        auto end = get_now();
        std::cout << "      io_uring waited for "
                  << (static_cast<double>(
                          std::chrono::duration_cast<std::chrono::microseconds>(
                              end - begin)
                              .count()) /
                      1000.0)
                  << " ms." << std::endl;
        if constexpr (requires { timeout.count(); }) {
            auto diff = end - begin;
            EXPECT_GE(diff, timeout);
            EXPECT_LT(diff, timeout + std::chrono::milliseconds(100));
        }
        else {
            EXPECT_GE(end, timeout);
            EXPECT_LT(end, timeout + std::chrono::milliseconds(100));
        }
    };
    check(
        "Relative delay",
        [] { return std::chrono::steady_clock::now(); },
        std::chrono::milliseconds(100));
    check(
        "Absolute monotonic deadline",
        [] { return std::chrono::steady_clock::now(); },
        std::chrono::steady_clock::now() + std::chrono::milliseconds(100));
    check(
        "Absolute UTC deadline",
        [] { return std::chrono::system_clock::now(); },
        std::chrono::system_clock::now() + std::chrono::milliseconds(100));
    check(
        "Instant",
        [] { return std::chrono::steady_clock::now(); },
        std::chrono::milliseconds(0));
}

TEST_F(AsyncIO, threadsafe_sender_receiver)
{
    using namespace MONAD_ASYNC_NAMESPACE;

    struct receiver_t
    {
        std::atomic<bool> done{false};
        receiver_t() = default;

        receiver_t(receiver_t const &) {}

        void set_value(erased_connected_operation *, result<void> res)
        {
            ASSERT_TRUE(res);
            done = true;
        }
    };

    auto state =
        connect(*shared_state_()->testio, threadsafe_sender{}, receiver_t{});
    auto fut = std::async(std::launch::async, [&state] { state.initiate(); });
    while (!state.receiver().done) {
        shared_state_()->testio->poll_blocking(1);
    }
    fut.get();
}

TEST_F(AsyncIO, read_multiple_buffer_sender_receiver)
{
    using namespace MONAD_ASYNC_NAMESPACE;

    struct receiver_t
    {
        std::optional<read_multiple_buffer_sender::buffers_type> &v;

        void set_value(
            erased_connected_operation *,
            read_multiple_buffer_sender::result_type res)
        {
            ASSERT_TRUE(res);
            v = std::move(res).assume_value();
        }

        void reset() {}
    };

    std::byte *buffer =
        (std::byte *)aligned_alloc(DISK_PAGE_SIZE, DISK_PAGE_SIZE * 4);
    auto unbuffer = monad::make_scope_exit([&]() noexcept { free(buffer); });
    std::vector<read_multiple_buffer_sender::buffer_type> inbuffers;
    inbuffers.emplace_back(buffer + 0, DISK_PAGE_SIZE);
    inbuffers.emplace_back(buffer + DISK_PAGE_SIZE, DISK_PAGE_SIZE);
    inbuffers.emplace_back(buffer + DISK_PAGE_SIZE * 2, DISK_PAGE_SIZE * 2);
    std::optional<read_multiple_buffer_sender::buffers_type> outbuffers;
    auto state = connect(
        *shared_state_()->testio,
        read_multiple_buffer_sender{{0, 0}, inbuffers},
        receiver_t{outbuffers});
    state.initiate();
    while (!outbuffers) {
        shared_state_()->testio->poll_blocking(1);
    }
    ASSERT_EQ(outbuffers->size(), 3);
    EXPECT_EQ((*outbuffers)[0].data(), buffer);
    EXPECT_EQ((*outbuffers)[0].size(), DISK_PAGE_SIZE);
    EXPECT_EQ(
        0,
        memcmp(
            (*outbuffers)[0].data(),
            shared_state_()->testfilecontents.data(),
            DISK_PAGE_SIZE));
    EXPECT_EQ((*outbuffers)[1].data(), buffer + DISK_PAGE_SIZE);
    EXPECT_EQ((*outbuffers)[1].size(), DISK_PAGE_SIZE);
    EXPECT_EQ(
        0,
        memcmp(
            (*outbuffers)[0].data() + DISK_PAGE_SIZE,
            shared_state_()->testfilecontents.data() + DISK_PAGE_SIZE,
            DISK_PAGE_SIZE));
    EXPECT_EQ((*outbuffers)[2].data(), buffer + DISK_PAGE_SIZE * 2);
    EXPECT_EQ((*outbuffers)[2].size(), DISK_PAGE_SIZE * 2);
    EXPECT_EQ(
        0,
        memcmp(
            (*outbuffers)[0].data() + DISK_PAGE_SIZE * 2,
            shared_state_()->testfilecontents.data() + DISK_PAGE_SIZE * 2,
            DISK_PAGE_SIZE * 2));

    outbuffers.reset();
    state.reset(
        std::tuple(
            chunk_offset_t{
                0,
                shared_state_()->testfilecontents.size() - DISK_PAGE_SIZE * 4},
            read_multiple_buffer_sender::buffers_type{inbuffers}),
        std::tuple());
    state.initiate();
    while (!outbuffers) {
        shared_state_()->testio->poll_blocking(1);
    }
    ASSERT_EQ(outbuffers->size(), 3);
    EXPECT_EQ((*outbuffers)[0].data(), buffer);
    EXPECT_EQ((*outbuffers)[0].size(), DISK_PAGE_SIZE);
    EXPECT_EQ(
        0,
        memcmp(
            (*outbuffers)[0].data(),
            shared_state_()->testfilecontents.data() +
                shared_state_()->testfilecontents.size() - DISK_PAGE_SIZE * 4,
            DISK_PAGE_SIZE));
    EXPECT_EQ((*outbuffers)[1].data(), buffer + DISK_PAGE_SIZE);
    EXPECT_EQ((*outbuffers)[1].size(), DISK_PAGE_SIZE);
    EXPECT_EQ(
        0,
        memcmp(
            (*outbuffers)[0].data() + DISK_PAGE_SIZE,
            shared_state_()->testfilecontents.data() +
                shared_state_()->testfilecontents.size() - DISK_PAGE_SIZE * 3,
            DISK_PAGE_SIZE));
    EXPECT_EQ((*outbuffers)[2].data(), buffer + DISK_PAGE_SIZE * 2);
    EXPECT_EQ((*outbuffers)[2].size(), DISK_PAGE_SIZE * 2);
    EXPECT_EQ(
        0,
        memcmp(
            (*outbuffers)[0].data() + DISK_PAGE_SIZE * 2,
            shared_state_()->testfilecontents.data() +
                shared_state_()->testfilecontents.size() - DISK_PAGE_SIZE * 2,
            DISK_PAGE_SIZE * 2));
}

// Works around a bug in clang's Release mode optimiser
namespace benchmark_non_zero_timeout_sender_receiver_ns
{
    using namespace MONAD_ASYNC_NAMESPACE;

    static std::atomic<int> done{0};
    static size_t count = 0;

    struct reinitiating_receiver_t
    {
        void set_value(erased_connected_operation *state, result<void> res)
        {
            ASSERT_TRUE(res);
            count++;
            if (!done) {
                state->initiate();
            }
        }
    };

    void benchmark(char const *desc, auto &shared_state, auto &&initiate)
    {
        std::cout << "Benchmarking " << desc << " ..." << std::endl;
        done = false;
        count = 0;
        auto begin = std::chrono::steady_clock::now();
        auto end = begin;
        initiate();
        for (; end - begin < std::chrono::seconds(5);
             end = std::chrono::steady_clock::now()) {
            shared_state->testio->poll_blocking(256);
        }
        done = true;
        std::cout << "   Waiting until done ..." << std::endl;
        shared_state->testio->wait_until_done();
        end = std::chrono::steady_clock::now();
        auto diff =
            std::chrono::duration_cast<std::chrono::milliseconds>(end - begin);
        std::cout << "   Did "
                  << (1000.0 * static_cast<double>(count) /
                      static_cast<double>(diff.count()))
                  << " completions per second" << std::endl;
    };
}

namespace benchmark_zero_timeout_sender_receiver_ns
{
    using namespace MONAD_ASYNC_NAMESPACE;
    static std::atomic<int> done{0};
    static size_t count = 0;

    struct reinitiating_receiver_t
    {
        void set_value(erased_connected_operation *state, result<void> res)
        {
            ASSERT_TRUE(res);
            count++;
            if (!done) {
                state->initiate();
            }
        }
    };

    void benchmark(char const *desc, auto &shared_state, auto &&initiate)
    {
        std::cout << "Benchmarking " << desc << " ..." << std::endl;
        done = false;
        count = 0;
        auto begin = std::chrono::steady_clock::now();
        auto end = begin;
        initiate();
        for (; end - begin < std::chrono::seconds(5);
             end = std::chrono::steady_clock::now()) {
            shared_state->testio->poll_blocking(256);
        }
        done = true;
        std::cout << "   Waiting until done ..." << std::endl;
        shared_state->testio->wait_until_done();
        end = std::chrono::steady_clock::now();
        auto diff =
            std::chrono::duration_cast<std::chrono::milliseconds>(end - begin);
        std::cout << "   Did "
                  << (1000.0 * static_cast<double>(count) /
                      static_cast<double>(diff.count()))
                  << " completions per second" << std::endl;
    };
}

TEST_F(AsyncIO, benchmark_zero_timeout_sender_receiver)
{
    using namespace benchmark_zero_timeout_sender_receiver_ns;
    static constexpr size_t COUNT = 1000;

    std::array<
        connected_operation<timed_delay_sender, reinitiating_receiver_t>,
        COUNT>
        states = monad::make_array<
            connected_operation<timed_delay_sender, reinitiating_receiver_t>,
            COUNT>(
            std::piecewise_construct,
            *shared_state_()->testio,
            timed_delay_sender(std::chrono::seconds(0)),
            reinitiating_receiver_t{});
    benchmark(
        "timed_delay_sender with a zero timeout", shared_state_(), [&states] {
            for (auto &i : states) {
                i.initiate();
            }
        });
}

/* A receiver which just immediately asks the sender
to reinitiate the i/o. This test models traditional
completion handler based i/o.
*/
struct completion_handler_io_receiver
{
    static constexpr bool lifetime_managed_internally = false;

    read_single_buffer_operation_states_base_ *state;

    explicit completion_handler_io_receiver(
        read_single_buffer_operation_states_base_ *s)
        : state(s)
    {
    }

    void set_value(
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *rawstate,
        MONAD_ASYNC_NAMESPACE::read_single_buffer_sender::result_type buffer)
    {
        ASSERT_TRUE(buffer);
        state->reinitiate(rawstate, std::move(buffer.assume_value().get()));
    }

    void reset() {}
};

TEST_F(AsyncIO, completion_handler_sender_receiver)
{
    using namespace MONAD_ASYNC_NAMESPACE;
    read_single_buffer_operation_states_<completion_handler_io_receiver> states(
        shared_state_().get(), MAX_CONCURRENCY);
    auto begin = std::chrono::steady_clock::now();
    auto end = begin;
    states.initiate();
    for (; end - begin < std::chrono::seconds(5);
         end = std::chrono::steady_clock::now()) {
        shared_state_()->testio->poll_blocking(256);
    }
    states.stop();
    end = std::chrono::steady_clock::now();
    auto diff =
        std::chrono::duration_cast<std::chrono::milliseconds>(end - begin);
    std::cout << "Did "
              << (1000.0 * states.count() / static_cast<double>(diff.count()))
              << " random single byte reads per second from file length "
              << (TEST_FILE_SIZE / 1024 / 1024) << " Mb" << std::endl;
}

#if __GNUC__ == 12
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
#endif
/* A receiver which suspends and resumes a C++ coroutine
 */
struct cpp_suspend_resume_io_receiver
{
    static constexpr bool lifetime_managed_internally = false;

    using result_type = std::pair<
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *,
        MONAD_ASYNC_NAMESPACE::read_single_buffer_sender::result_type>;
    std::coroutine_handle<> _h;
    std::optional<result_type> res;

    explicit cpp_suspend_resume_io_receiver(
        read_single_buffer_operation_states_base_ *)
    {
    }

    void set_value(
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *rawstate,
        MONAD_ASYNC_NAMESPACE::read_single_buffer_sender::result_type buffer)
    {
        MONAD_DEBUG_ASSERT(!res.has_value());
        res = {rawstate, std::move(buffer)};
        _h.resume();
    }

    void reset()
    {
        _h = {};
        res.reset();
    }

    // This is the C++ coroutine machinery which declares
    // that this type is an awaitable
    bool await_ready() const noexcept
    {
        return res.has_value();
    }

    void await_suspend(std::coroutine_handle<> h)
    {
        MONAD_DEBUG_ASSERT(!res.has_value());
        _h = h;
    }

    result_type await_resume()
    {
        MONAD_DEBUG_ASSERT(res.has_value());
        auto ret = std::move(res).value();
        res.reset();
        return ret;
    }
};
#if __GNUC__ == 12
    #pragma GCC diagnostic pop
#endif

TEST_F(AsyncIO, cpp_coroutine_sender_receiver)
{
    using namespace MONAD_ASYNC_NAMESPACE;
    read_single_buffer_operation_states_<cpp_suspend_resume_io_receiver> states(
        shared_state_().get(), MAX_CONCURRENCY);
    auto begin = std::chrono::steady_clock::now();
    auto end = begin;
    auto coroutine = [&](cpp_suspend_resume_io_receiver &receiver)
        -> BOOST_OUTCOME_V2_NAMESPACE::awaitables::eager<void> {
        for (;;) {
            auto [rawstate, buffer] = co_await receiver;
            // Can't use gtest ASSERT_TRUE here as it is not coroutine
            // compatible
            if (!buffer) {
                abort();
            }
            if (!states.reinitiate(
                    rawstate, std::move(buffer.assume_value().get()))) {
                co_return;
            }
        }
    };
    std::vector<BOOST_OUTCOME_V2_NAMESPACE::awaitables::eager<void>> awaitables;
    awaitables.reserve(MAX_CONCURRENCY);
    for (size_t n = 0; n < MAX_CONCURRENCY; n++) {
        awaitables.push_back(coroutine(states.receiver(n)));
    }
    states.initiate();
    for (; end - begin < std::chrono::seconds(5);
         end = std::chrono::steady_clock::now()) {
        shared_state_()->testio->poll_blocking(256);
    }
    states.stop();
    awaitables.clear();
    end = std::chrono::steady_clock::now();
    auto diff =
        std::chrono::duration_cast<std::chrono::milliseconds>(end - begin);
    std::cout << "Did "
              << (1000.0 * static_cast<double>(states.count()) /
                  static_cast<double>(diff.count()))
              << " random single byte reads per second from file length "
              << (TEST_FILE_SIZE / 1024 / 1024) << " Mb" << std::endl;
}

/* A receiver which suspends and resumes a Boost.Fiber
 */
struct fiber_suspend_resume_io_receiver
{
    static constexpr bool lifetime_managed_internally = false;

    using result_type = std::pair<
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *,
        MONAD_ASYNC_NAMESPACE::read_single_buffer_sender::result_type>;
    boost::fibers::promise<result_type> promise;

    explicit fiber_suspend_resume_io_receiver(
        read_single_buffer_operation_states_base_ *)
    {
    }

    void set_value(
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *rawstate,
        MONAD_ASYNC_NAMESPACE::read_single_buffer_sender::result_type buffer)
    {
        promise.set_value({rawstate, std::move(buffer)});
    }

    void reset()
    {
        promise = {};
    }
};

TEST_F(AsyncIO, fiber_sender_receiver)
{
    using namespace MONAD_ASYNC_NAMESPACE;
    read_single_buffer_operation_states_<fiber_suspend_resume_io_receiver>
        states(shared_state_().get(), MAX_CONCURRENCY);
    auto begin = std::chrono::steady_clock::now();
    auto end = begin;
    auto fiber = [&](fiber_suspend_resume_io_receiver *receiver) {
        for (;;) {
            auto future = receiver->promise.get_future();
            auto [rawstate, buffer] = future.get();
            ASSERT_TRUE(buffer);
            if (!states.reinitiate(
                    rawstate, std::move(buffer.assume_value().get()))) {
                return;
            }
        }
    };
    std::vector<boost::fibers::fiber> fibers;
    fibers.reserve(MAX_CONCURRENCY);
    for (size_t n = 0; n < MAX_CONCURRENCY; n++) {
        fibers.emplace_back(fiber, &states.receiver(n));
    }
    states.initiate();
    for (; end - begin < std::chrono::seconds(5);
         end = std::chrono::steady_clock::now()) {
        boost::this_fiber::yield();
        shared_state_()->testio->poll_blocking(256);
    }
    states.stop();
    for (auto &i : fibers) {
        i.join();
    }
    fibers.clear();
    end = std::chrono::steady_clock::now();
    auto diff =
        std::chrono::duration_cast<std::chrono::milliseconds>(end - begin);
    std::cout << "Did "
              << (1000.0 * static_cast<double>(states.count()) /
                  static_cast<double>(diff.count()))
              << " random single byte reads per second from file length "
              << (TEST_FILE_SIZE / 1024 / 1024) << " Mb" << std::endl;
}

TEST_F(AsyncIO, stack_overflow_avoided)
{
    using namespace MONAD_ASYNC_NAMESPACE;
    static constexpr size_t COUNT = 100000;
    struct receiver_t;
    static std::vector<std::unique_ptr<erased_connected_operation>> ops;
    static unsigned stack_depth = 0;
    static unsigned counter = 0;
    ops.reserve(COUNT);

    struct receiver_t
    {
        unsigned count;

        void set_value(erased_connected_operation *, result<void> res)
        {
            static thread_local unsigned stack_level = 0;
            ASSERT_TRUE(res);
            if (ops.size() < COUNT) {
                // Initiate another two operations to create a combinatorial
                // explosion
                using unique_ptr_type = MONAD_ASYNC_NAMESPACE::AsyncIO::
                    connected_operation_unique_ptr_type<
                        timed_delay_sender,
                        receiver_t>;
                auto initiate = [] {
                    unique_ptr_type p(new unique_ptr_type::element_type(connect(
                        *shared_state_()->testio,
                        timed_delay_sender(std::chrono::seconds(0)),
                        receiver_t{counter++})));
                    p->initiate();
                    ops.push_back(std::unique_ptr<erased_connected_operation>(
                        p.release()));
                };
                if (stack_level > stack_depth) {
                    std::cout << "Stack depth reaches " << stack_level
                              << std::endl;
                    stack_depth = stack_level;
                }
                EXPECT_LT(stack_level, 2);
                stack_level++;
                initiate();
                initiate();
                stack_level--;
            }
        }
    };

    receiver_t{counter++}.set_value(nullptr, success());
    shared_state_()->testio->wait_until_done();
    EXPECT_GE(ops.size(), COUNT);
}

TEST_F(AsyncIO, erased_complete_overloads_decay_to_void)
{
    using namespace MONAD_ASYNC_NAMESPACE;

    struct void_sender
    {
        using result_type = result<void>;

        result<void> operator()(erased_connected_operation *) noexcept
        {
            return success();
        }

        void reset() {}
    };

    struct void_receiver
    {
        std::optional<result<void>> &out;

        void set_value(erased_connected_operation *, result<void> res)
        {
            out = std::move(res);
        }

        void reset() {}
    };

    // void
    std::optional<result<void>> out;
    auto state = connect(void_sender{}, void_receiver{out});
    state.initiate();
    state.completed(success());
    ASSERT_TRUE(out.has_value());
    EXPECT_TRUE(*out);

    out.reset();
    state.reset(std::tuple{}, std::tuple{});
    state.initiate();
    state.completed(result<void>(errc::address_in_use));
    ASSERT_TRUE(out.has_value());
    ASSERT_FALSE(*out);
    ASSERT_EQ(out->error(), errc::address_in_use);

    // size_t
    out.reset();
    state.reset(std::tuple{}, std::tuple{});
    state.initiate();
    state.completed(5);
    ASSERT_TRUE(out.has_value());
    EXPECT_TRUE(*out); // value is thrown away, but is successful

    out.reset();
    state.reset(std::tuple{}, std::tuple{});
    state.initiate();
    state.completed(result<size_t>(errc::address_in_use));
    ASSERT_TRUE(out.has_value());
    ASSERT_FALSE(*out);
    ASSERT_EQ(out->error(), errc::address_in_use);

    // filled_read_buffer
    filled_read_buffer rb(5);
    out.reset();
    state.reset(std::tuple{}, std::tuple{});
    state.initiate();
    state.completed(result<std::reference_wrapper<filled_read_buffer>>(rb));
    ASSERT_TRUE(out.has_value());
    EXPECT_TRUE(*out); // value is thrown away, but is successful

    out.reset();
    state.reset(std::tuple{}, std::tuple{});
    state.initiate();
    state.completed(result<std::reference_wrapper<filled_read_buffer>>(
        errc::address_in_use));
    ASSERT_TRUE(out.has_value());
    ASSERT_FALSE(*out);
    ASSERT_EQ(out->error(), errc::address_in_use);

    // filled_write_buffer
    filled_write_buffer wb(5);
    out.reset();
    state.reset(std::tuple{}, std::tuple{});
    state.initiate();
    state.completed(result<std::reference_wrapper<filled_write_buffer>>(wb));
    ASSERT_TRUE(out.has_value());
    EXPECT_TRUE(*out); // value is thrown away, but is successful

    out.reset();
    state.reset(std::tuple{}, std::tuple{});
    state.initiate();
    state.completed(result<std::reference_wrapper<filled_write_buffer>>(
        errc::address_in_use));
    ASSERT_TRUE(out.has_value());
    ASSERT_FALSE(*out);
    ASSERT_EQ(out->error(), errc::address_in_use);
}

TEST_F(AsyncIO, erased_complete_overloads_decay_to_bytes_transferred)
{
    using namespace MONAD_ASYNC_NAMESPACE;

    struct bytes_transferred_sender
    {
        using result_type = result<size_t>;

        result<void> operator()(erased_connected_operation *) noexcept
        {
            return success();
        }

        void reset() {}
    };

    struct bytes_transferred_receiver
    {
        std::optional<result<size_t>> &out;

        void set_value(erased_connected_operation *, result<size_t> res)
        {
            out = std::move(res);
        }

        void reset() {}
    };

    // size_t
    std::optional<result<size_t>> out;
    auto state =
        connect(bytes_transferred_sender{}, bytes_transferred_receiver{out});
    state.initiate();
    state.completed(5);
    ASSERT_TRUE(out.has_value());
    EXPECT_EQ(out->value(), 5);

    out.reset();
    state.reset(std::tuple{}, std::tuple{});
    state.initiate();
    state.completed(result<size_t>(errc::address_in_use));
    ASSERT_TRUE(out.has_value());
    ASSERT_FALSE(*out);
    ASSERT_EQ(out->error(), errc::address_in_use);

    // filled_read_buffer
    filled_read_buffer rb(5);
    out.reset();
    state.reset(std::tuple{}, std::tuple{});
    state.initiate();
    state.completed(result<std::reference_wrapper<filled_read_buffer>>(rb));
    ASSERT_TRUE(out.has_value());
    EXPECT_EQ(out->value(), 5);

    out.reset();
    state.reset(std::tuple{}, std::tuple{});
    state.initiate();
    state.completed(result<std::reference_wrapper<filled_read_buffer>>(
        errc::address_in_use));
    ASSERT_TRUE(out.has_value());
    ASSERT_FALSE(*out);
    ASSERT_EQ(out->error(), errc::address_in_use);

    // filled_write_buffer
    filled_write_buffer wb(5);
    out.reset();
    state.reset(std::tuple{}, std::tuple{});
    state.initiate();
    state.completed(result<std::reference_wrapper<filled_write_buffer>>(wb));
    ASSERT_TRUE(out.has_value());
    EXPECT_EQ(out->value(), 5);

    out.reset();
    state.reset(std::tuple{}, std::tuple{});
    state.initiate();
    state.completed(result<std::reference_wrapper<filled_write_buffer>>(
        errc::address_in_use));
    ASSERT_TRUE(out.has_value());
    ASSERT_FALSE(*out);
    ASSERT_EQ(out->error(), errc::address_in_use);
}

TEST_F(AsyncIO, immediate_completion_decays_to_bytes_transferred)
{
    using namespace MONAD_ASYNC_NAMESPACE;

    struct void_sender
    {
        using result_type = result<void>;

        std::variant<
            std::monostate, size_t, filled_read_buffer, filled_write_buffer>
            payload_to_immediately_complete;

        result<void> operator()(erased_connected_operation *) noexcept
        {
            return std::visit(
                [&](auto &v) -> result<void> {
                    using type = std::decay_t<decltype(v)>;
                    if constexpr (std::is_same_v<type, std::monostate>) {
                        return make_status_code(
                            sender_errc::initiation_immediately_completed);
                    }
                    else {
                        return make_status_code(
                            sender_errc::initiation_immediately_completed,
                            std::ref(v));
                    }
                },
                payload_to_immediately_complete);
        }

        void reset(size_t v)
        {
            payload_to_immediately_complete = v;
        }

        void reset(filled_read_buffer v)
        {
            payload_to_immediately_complete = std::move(v);
        }

        void reset(filled_write_buffer v)
        {
            payload_to_immediately_complete = std::move(v);
        }
    };

    struct void_receiver
    {
        std::optional<result<void>> &out;

        void set_value(erased_connected_operation *, result<void> res)
        {
            out = std::move(res);
        }

        void reset() {}
    };

    // void
    std::optional<result<void>> out;
    auto state = connect(void_sender{}, void_receiver{out});
    state.initiate();
    ASSERT_TRUE(out.has_value());
    EXPECT_TRUE(*out);

    // size_t
    out.reset();
    state.reset(std::tuple{5u}, std::tuple{});
    state.initiate();
    ASSERT_TRUE(out.has_value());
    EXPECT_TRUE(*out); // value is thrown away, but is successful

    // filled_read_buffer
    out.reset();
    state.reset(std::tuple{filled_read_buffer(5)}, std::tuple{});
    state.initiate();
    ASSERT_TRUE(out.has_value());
    EXPECT_TRUE(*out); // value is thrown away, but is successful

    // filled_write_buffer
    out.reset();
    state.reset(std::tuple{filled_write_buffer(5)}, std::tuple{});
    state.initiate();
    ASSERT_TRUE(out.has_value());
    EXPECT_TRUE(*out); // value is thrown away, but is successful
}

TEST_F(AsyncIO, immediate_completion_decays_to_void)
{
    using namespace MONAD_ASYNC_NAMESPACE;

    struct bytes_transferred_sender
    {
        using result_type = result<size_t>;

        std::variant<
            std::monostate, size_t, filled_read_buffer, filled_write_buffer>
            payload_to_immediately_complete;

        result<void> operator()(erased_connected_operation *) noexcept
        {
            return std::visit(
                [&](auto &v) -> result<void> {
                    using type = std::decay_t<decltype(v)>;
                    if constexpr (std::is_same_v<type, std::monostate>) {
                        return make_status_code(
                            sender_errc::initiation_immediately_completed);
                    }
                    else {
                        return make_status_code(
                            sender_errc::initiation_immediately_completed,
                            std::ref(v));
                    }
                },
                payload_to_immediately_complete);
        }

        void reset(size_t v)
        {
            payload_to_immediately_complete = v;
        }

        void reset(filled_read_buffer v)
        {
            payload_to_immediately_complete = std::move(v);
        }

        void reset(filled_write_buffer v)
        {
            payload_to_immediately_complete = std::move(v);
        }
    };

    struct bytes_transferred_receiver
    {
        std::optional<result<size_t>> &out;

        void set_value(erased_connected_operation *, result<size_t> res)
        {
            out = std::move(res);
        }

        void reset() {}
    };

    // void
    std::optional<result<size_t>> out;
    auto state =
        connect(bytes_transferred_sender{5u}, bytes_transferred_receiver{out});
    state.initiate();
    ASSERT_TRUE(out.has_value());
    EXPECT_EQ(out->value(), 5);

    // filled_read_buffer
    out.reset();
    state.reset(std::tuple{filled_read_buffer(5)}, std::tuple{});
    state.initiate();
    ASSERT_TRUE(out.has_value());
    EXPECT_EQ(out->value(), 5);

    // filled_write_buffer
    out.reset();
    state.reset(std::tuple{filled_write_buffer(5)}, std::tuple{});
    state.initiate();
    ASSERT_TRUE(out.has_value());
    EXPECT_EQ(out->value(), 5);
}
