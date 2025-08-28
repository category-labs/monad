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

#include <category/core/monad_exception.hpp>

#include <gtest/gtest.h>

#include <cstring>
#include <unistd.h>

using namespace monad;

namespace
{
    TEST(MonadExceptionTest, message_empty)
    {
        try {
            MONAD_ASSERT_THROW(false, "");
        } catch (MonadException const &e) {
            ASSERT_TRUE(std::strcmp(e.message(), "") == 0);
            return;
        }
        FAIL();
    }

    TEST(MonadExceptionTest, message_size_max)
    {
        char message[MonadException::message_buffer_size];
        for (size_t i = 0; i < sizeof(message) - 1; ++i) {
            message[i] = static_cast<char>('0' + i % 10);
        }
        message[MonadException::message_buffer_size - 1] = '\0';
        try {
            MONAD_ASSERT_THROW(false, message);
        } catch (MonadException const &e) {
            ASSERT_TRUE(std::strcmp(e.message(), message) == 0);
            return;
        }
        FAIL();
    }

    TEST(MonadExceptionTest, message_size_out_of_bound)
    {
        char message[MonadException::message_buffer_size + 1];
        for (size_t i = 0; i < sizeof(message) - 1; ++i) {
            message[i] = static_cast<char>('0' + i % 10);
        }
        message[MonadException::message_buffer_size] = '\0';
        try {
            MONAD_ASSERT_THROW(false, message);
        } catch (MonadException const &e) {
            message[MonadException::message_buffer_size - 1] = '\0';
            ASSERT_TRUE(std::strcmp(e.message(), message) == 0);
            return;
        }
        FAIL();
    }

    TEST(MonadExceptionTest, print)
    {
        try {
            MONAD_ASSERT_THROW(false, "hello world");
        } catch (MonadException const &e) {
            int fds[2];
            int r = ::pipe(fds);
            ASSERT_NE(r, -1);

            e.print(fds[1]);

            char buffer[MonadException::stack_trace_buffer_size + 256];
            ssize_t const n = ::read(fds[0], buffer, sizeof(buffer));

            ASSERT_GT(n, 0);
            ASSERT_LT(n, sizeof(buffer));

            buffer[static_cast<size_t>(n)] = '\0';

            ASSERT_NE(nullptr, strstr(buffer, "hello world"));
            ASSERT_NE(nullptr, strstr(buffer, "/test/monad_exception.cpp"));

            ::close(fds[0]);
            ::close(fds[1]);
            return;
        }
        FAIL();
    }
}
