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

#if defined(__GNUC__) && !defined(__clang__)
    #pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
#endif

#include "test_fixture.hpp"

#include <category/async/concepts.hpp>
#include <category/async/config.hpp>
#include <category/async/connected_operation.hpp>
#include <category/async/detail/scope_polyfill.hpp>
#include <category/async/erased_connected_operation.hpp>
#include <category/async/io.hpp>
#include <category/async/io_senders.hpp>
#include <category/async/sender_errc.hpp>
#include <category/async/util.hpp>
#include <category/core/assert.h>
#include <category/core/small_prng.hpp>

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
#include <cassert>
#include <chrono>
#include <coroutine>
#include <cstddef>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <ostream>
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
    auto const unbuffer =
        monad::make_scope_exit([&]() noexcept { free(buffer); });
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
    auto const begin = std::chrono::steady_clock::now();
    auto end = begin;
    states.initiate();
    for (; end - begin < std::chrono::seconds(5);
         end = std::chrono::steady_clock::now()) {
        shared_state_()->testio->poll_blocking(256);
    }
    states.stop();
    end = std::chrono::steady_clock::now();
    auto const diff =
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
        MONAD_ASSERT(!res.has_value());
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
        MONAD_ASSERT(!res.has_value());
        _h = h;
    }

    result_type await_resume()
    {
        MONAD_ASSERT(res.has_value());
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
    auto const begin = std::chrono::steady_clock::now();
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
    auto const diff =
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
    auto const begin = std::chrono::steady_clock::now();
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
    auto const diff =
        std::chrono::duration_cast<std::chrono::milliseconds>(end - begin);
    std::cout << "Did "
              << (1000.0 * static_cast<double>(states.count()) /
                  static_cast<double>(diff.count()))
              << " random single byte reads per second from file length "
              << (TEST_FILE_SIZE / 1024 / 1024) << " Mb" << std::endl;
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

        // NOLINTNEXTLINE(bugprone-exception-escape): `std::visit` won't throw
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

        // NOLINTNEXTLINE(bugprone-exception-escape): `std::visit` won't throw
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
