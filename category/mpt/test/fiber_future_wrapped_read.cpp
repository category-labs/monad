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

#include "test_fixtures_gtest.hpp" // NOLINT

#include <category/async/concepts.hpp>
#include <category/async/config.hpp>
#include <category/async/erased_connected_operation.hpp>
#include <category/async/io_senders.hpp>
#include <category/async/util.hpp>
#include <category/core/small_prng.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <boost/fiber/future/async.hpp>
#include <boost/fiber/future/future.hpp>
#include <boost/fiber/future/future_status.hpp>
#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>

#include <chrono>
#include <cstddef>
#include <cstring>
#include <iostream>
#include <ostream>
#include <utility>
#include <vector>

using namespace MONAD_ASYNC_NAMESPACE;

namespace
{
    struct FiberFutureWrappedFind
        : public monad::test::AsyncTestFixture<::testing::Test>
    {
    };

    struct receiver_t
    {
        FiberFutureWrappedFind::shared_state_t *const fixture_shared_state;
        ::boost::fibers::promise<
            MONAD_ASYNC_NAMESPACE::read_single_buffer_sender::buffer_type>
            promise;
        chunk_offset_t offset;

        static constexpr bool lifetime_managed_internally =
            false; // we manage state lifetime

        bool done{false};

        receiver_t(
            FiberFutureWrappedFind::shared_state_t *fixture_shared_state_,
            ::boost::fibers::promise<
                MONAD_ASYNC_NAMESPACE::read_single_buffer_sender::buffer_type>
                &&p,
            chunk_offset_t const offset_)
            : fixture_shared_state(fixture_shared_state_)
            , promise(std::move(p))
            , offset(offset_)
        {
        }

        void set_value(
            erased_connected_operation *,
            MONAD_ASYNC_NAMESPACE::read_single_buffer_sender::result_type res)
        {
            ASSERT_TRUE(res);
            auto &buffer = res.assume_value().get();

            EXPECT_EQ(
                buffer.front(),
                fixture_shared_state->testfilecontents[offset.offset]);

            promise.set_value(std::move(buffer));
            done = true;
        }
    };
}

TEST_F(FiberFutureWrappedFind, single_thread_fibers_read)
{
    // impl_sender: request read thru an io sender
    auto impl_sender = [&]() -> result<std::vector<std::byte>> {
        // This initiates the i/o reading DISK_PAGE_SIZE bytes from a
        // randomized offset
        using promise_result_t =
            MONAD_ASYNC_NAMESPACE::read_single_buffer_sender::buffer_type;

        chunk_offset_t const offset(
            0,
            round_down_align<DISK_PAGE_BITS>(
                shared_state_()->test_rand() %
                (TEST_FILE_SIZE - DISK_PAGE_SIZE)));
        auto sender = read_single_buffer_sender(offset, DISK_PAGE_SIZE);
        ::boost::fibers::promise<promise_result_t> promise;
        auto fut = promise.get_future();
        auto iostate = shared_state_()->testio->make_connected(
            std::move(sender),
            receiver_t{shared_state_().get(), std::move(promise), offset});
        iostate->initiate();
        std::cout << "sender..." << std::endl;

        auto bytesread = fut.get();
        // Return a copy of the registered buffer with lifetime held by fut
        return std::vector<std::byte>(bytesread.begin(), bytesread.end());
    };

    // Launch the fiber task
    std::vector<::boost::fibers::future<result<std::vector<std::byte>>>>
        futures;
    futures.reserve(MAX_CONCURRENCY);
    for (size_t i = 0; i < MAX_CONCURRENCY; ++i) {
        futures.emplace_back(::boost::fibers::async(impl_sender));
    }

    // Pump the loop until the fiber completes
    for (auto &fut : futures) {
        while (::boost::fibers::future_status::ready !=
               fut.wait_for(std::chrono::seconds(0))) {
            shared_state_()->testio->poll_nonblocking(1);
        }
        auto res = fut.get();
    }
}
