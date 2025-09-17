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

#include <category/async/concepts.hpp>
#include <category/async/config.hpp>
#include <category/async/detail/scope_polyfill.hpp>
#include <category/async/erased_connected_operation.hpp>
#include <category/async/io.hpp>
#include <category/async/io_senders.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/assert.h>
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>

#include <gtest/gtest.h>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <cstddef>
#include <iostream>
#include <utility>
#include <vector>

namespace
{
    TEST(AsyncIODeathTest, write_buffer_exhaustion_causes_death)
    {
        monad::async::storage_pool pool(
            monad::async::use_anonymous_inode_tag{});
        monad::io::Ring testring1;
        monad::io::Ring testring2(1);
        monad::io::Buffers testrwbuf =
            monad::io::make_buffers_for_segregated_read_write(
                testring1,
                testring2,
                1,
                1,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testrwbuf);
        std::vector<monad::async::erased_connected_operation_ptr> states;
        auto empty_testio = monad::make_scope_exit(
            [&]() noexcept { testio.wait_until_done(); });

        struct empty_receiver
        {
            void set_value(
                monad::async::erased_connected_operation *,
                monad::async::write_single_buffer_sender::result_type r)
            {
                MONAD_ASSERT(r);
            }
        };

        for (size_t n = 0; n < 10; n++) {
            auto make = [&] {
                auto state(testio.make_connected(
                    monad::async::write_single_buffer_sender(
                        {0, 0}, monad::async::DISK_PAGE_SIZE),
                    empty_receiver{}));
                // Exactly the same test as the non-death test, except for this
                // line
                // state->initiate();
                states.push_back(std::move(state));
            };
            if (n > 0) {
                std::cerr << "Must fail after this:" << std::endl;
                make();
            }
            else {
                make();
            }
        }
    }
}
