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

#pragma once

#include "gtest/gtest.h"

#include <category/async/io.hpp>

#include <category/core/small_prng.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

namespace monad::test
{
    template <class Base>
    struct AsyncTestFixture : public Base
    {
        static constexpr size_t TEST_FILE_SIZE = 1024 * 1024;
        static constexpr size_t MAX_CONCURRENCY = 4;

        struct shared_state_t
        {
            static monad::io::Ring make_ring()
            {
                return monad::io::Ring({MAX_CONCURRENCY, false, 0});
            }

            static monad::io::Buffers make_buffers(monad::io::Ring &ring)
            {
                return monad::io::make_buffers_for_read_only(
                    ring, MAX_CONCURRENCY, 1UL << 13);
            }

            std::vector<std::byte> const testfilecontents = [] {
                std::vector<std::byte> ret(TEST_FILE_SIZE);
                std::span<
                    monad::small_prng::value_type,
                    TEST_FILE_SIZE / sizeof(monad::small_prng::value_type)>
                    s((monad::small_prng::value_type *)ret.data(),
                      TEST_FILE_SIZE / sizeof(monad::small_prng::value_type));
                monad::small_prng rand;
                for (auto &i : s) {
                    i = rand();
                }
                return ret;
            }();
            monad::async::storage_pool pool{
                monad::async::use_anonymous_inode_tag{}};
            monad::io::Ring testring = make_ring();
            monad::io::Buffers testrwbuf = make_buffers(testring);
            std::unique_ptr<monad::async::AsyncIO> testio = [this] {
                auto ret =
                    std::make_unique<monad::async::AsyncIO>(pool, testrwbuf);
                auto fd =
                    pool.activate_chunk(monad::async::storage_pool::seq, 0)
                        ->write_fd(TEST_FILE_SIZE);
                MONAD_ASSERT(
                    TEST_FILE_SIZE == ::pwrite(
                                          fd.first,
                                          testfilecontents.data(),
                                          TEST_FILE_SIZE,
                                          static_cast<off_t>(fd.second)));
                return ret;
            }();
            monad::small_prng test_rand;
        };

    protected:
        static std::unique_ptr<shared_state_t> &shared_state_()
        {
            static std::unique_ptr<shared_state_t> v;
            return v;
        }

        static void SetUpTestSuite()
        {
            shared_state_() = std::make_unique<shared_state_t>();
        }

        static void TearDownTestSuite()
        {
            shared_state_().reset();
        }
    };
}
