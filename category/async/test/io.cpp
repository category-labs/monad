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

#include "gtest/gtest.h"

#include <category/async/concepts.hpp>
#include <category/async/config.hpp>
#include <category/async/connected_operation.hpp>
#include <category/async/erased_connected_operation.hpp>
#include <category/async/io.hpp>
#include <category/async/io_senders.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/assert.h>
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <iostream>
#include <memory>
#include <optional>
#include <ostream>
#include <sys/types.h>
#include <system_error>
#include <utility>
#include <vector>

#include <unistd.h>

namespace
{
    struct empty_receiver
    {
        std::vector<monad::async::read_single_buffer_sender::buffer_type> &bufs;

        static constexpr bool lifetime_managed_internally = true;

        void set_value(
            monad::async::erased_connected_operation *,
            monad::async::read_single_buffer_sender::result_type r)
        {
            MONAD_ASSERT(r);
            // Exactly the same test as the death test, except for this line
            // bufs.emplace_back(std::move(r.assume_value().get()));
        }
    };

    TEST(AsyncIO, hardlink_fd_to)
    {
        monad::async::storage_pool pool(
            monad::async::use_anonymous_inode_tag{});
        {
            auto chunk = pool.chunk(pool.seq, 0);
            auto const fd = chunk.write_fd(1);
            char c = 5;
            MONAD_ASSERT(
                -1 != ::pwrite(fd.first, &c, 1, static_cast<off_t>(fd.second)));
        }
        monad::io::Ring testring(monad::io::RingConfig{1});
        monad::io::Buffers testrwbuf =
            monad::io::make_buffers_for_read_only(testring, 1, 1UL << 13);
        monad::async::AsyncIO testio(pool, testrwbuf);
        try {
            testio.dump_fd_to(0, "hardlink_fd_to_testname");
            EXPECT_TRUE(std::filesystem::exists("hardlink_fd_to_testname"));
        }
        catch (std::system_error const &e) {
            // If cross_device_link occurs, we are on a kernel before 5.3 which
            // doesn't suppose cross-filesystem copy_file_range()
            if (e.code() != std::errc::cross_device_link) {
                throw;
            }
        }
    }

    TEST(AsyncIO, buffer_exhaustion_pauses_until_io_completes_write)
    {
        monad::async::storage_pool pool(
            monad::async::use_anonymous_inode_tag{});
        monad::io::Ring testring1;
        monad::io::Ring testring2(monad::io::RingConfig{1});
        monad::io::Buffers testrwbuf =
            monad::io::make_buffers_for_segregated_read_write(
                testring1,
                testring2,
                1,
                1,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testrwbuf);

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
            auto state(testio.make_connected(
                monad::async::write_single_buffer_sender(
                    {0, 0}, monad::async::DISK_PAGE_SIZE),
                empty_receiver{}));
            // Exactly the same test as the death test, except for this line
            state->initiate(); // will reap completions if no buffers free
            (void)state.release();
        }
        testio.wait_until_done();
    }

    TEST(AsyncIO, buffer_exhaustion_pauses_until_io_completes_read)
    {
        monad::async::storage_pool pool(
            monad::async::use_anonymous_inode_tag{});
        monad::io::Ring testring;
        monad::io::Buffers testrwbuf = monad::io::make_buffers_for_read_only(
            testring, 1, monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE);
        monad::async::AsyncIO testio(pool, testrwbuf);
        static std::vector<monad::async::read_single_buffer_sender::buffer_type>
            bufs;

        for (size_t n = 0; n < 1000; n++) {
            auto state(testio.make_connected(
                monad::async::read_single_buffer_sender(
                    {0, 0}, monad::async::DISK_PAGE_SIZE),
                empty_receiver{bufs}));
            state->initiate(); // will reap completions if no buffers free
            (void)state.release();
        }
        testio.wait_until_done();
    }

    struct sqe_exhaustion_does_not_reorder_writes_receiver
    {
        static constexpr size_t COUNT = 128;

        uint32_t &offset;
        std::vector<monad::async::file_offset_t> &seq;

        inline void set_value(
            monad::async::erased_connected_operation *io_state,
            monad::async::write_single_buffer_sender::result_type r);
    };

    using sqe_exhaustion_does_not_reorder_writes_state_unique_ptr_type =
        monad::async::AsyncIO::connected_operation_unique_ptr_type<
            monad::async::write_single_buffer_sender,
            sqe_exhaustion_does_not_reorder_writes_receiver>;

    inline void sqe_exhaustion_does_not_reorder_writes_receiver::set_value(
        monad::async::erased_connected_operation *io_state,
        monad::async::write_single_buffer_sender::result_type r)
    {
        MONAD_ASSERT(r);
        auto *state = static_cast<
            sqe_exhaustion_does_not_reorder_writes_state_unique_ptr_type::
                element_type *>(io_state);
        seq.push_back(state->sender().offset().offset);
        if (seq.size() < COUNT) {
            auto s1 = state->executor()->make_connected(
                monad::async::write_single_buffer_sender(
                    {0, offset}, monad::async::DISK_PAGE_SIZE),
                sqe_exhaustion_does_not_reorder_writes_receiver{offset, seq});
            offset += monad::async::DISK_PAGE_SIZE;
            s1->sender().advance_buffer_append(monad::async::DISK_PAGE_SIZE);
            s1->initiate();
            (void)s1.release();
            auto s2 = state->executor()->make_connected(
                monad::async::write_single_buffer_sender(
                    {0, offset}, monad::async::DISK_PAGE_SIZE),
                sqe_exhaustion_does_not_reorder_writes_receiver{offset, seq});
            offset += monad::async::DISK_PAGE_SIZE;
            s2->sender().advance_buffer_append(monad::async::DISK_PAGE_SIZE);
            s2->initiate();
            (void)s2.release();
        }
    }

    TEST(AsyncIO, sqe_exhaustion_does_not_reorder_writes)
    {
        monad::async::storage_pool pool(
            monad::async::use_anonymous_inode_tag{});
        monad::io::Ring testring1(monad::io::RingConfig{4});
        monad::io::Ring testring2(
            {sqe_exhaustion_does_not_reorder_writes_receiver::COUNT,
             std::nullopt});
        monad::io::Buffers testrwbuf =
            monad::io::make_buffers_for_segregated_read_write(
                testring1,
                testring2,
                1,
                sqe_exhaustion_does_not_reorder_writes_receiver::COUNT,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testrwbuf);
        {
            auto const [max_sq_entries, max_cq_entries] =
                testio.io_uring_ring_entries_left(false);
            std::cout << "   non-write ring: sq entries created = "
                      << max_sq_entries
                      << " cq entries created = " << max_cq_entries
                      << std::endl;
        }
        {
            auto const [max_sq_entries, max_cq_entries] =
                testio.io_uring_ring_entries_left(true);
            std::cout << "       write ring: sq entries created = "
                      << max_sq_entries
                      << " cq entries created = " << max_cq_entries
                      << std::endl;
        }
        std::vector<monad::async::file_offset_t> seq;
        seq.reserve(sqe_exhaustion_does_not_reorder_writes_receiver::COUNT * 2);

        uint32_t offset = 0;
        auto s1 = testio.make_connected(
            monad::async::write_single_buffer_sender(
                {0, offset}, monad::async::DISK_PAGE_SIZE),
            sqe_exhaustion_does_not_reorder_writes_receiver{offset, seq});
        offset += monad::async::DISK_PAGE_SIZE;
        s1->sender().advance_buffer_append(monad::async::DISK_PAGE_SIZE);
        s1->initiate();
        (void)s1.release();
        testio.wait_until_done();
        std::cout << "   " << seq.size() << " offsets written." << std::endl;

        uint32_t offset2 = 0;
        for (auto const &i : seq) {
            EXPECT_EQ(i, offset2);
            offset2 += monad::async::DISK_PAGE_SIZE;
        }
        EXPECT_EQ(seq.back(), offset - monad::async::DISK_PAGE_SIZE);
    }

    struct concurrent_read_limit_receiver
    {
        size_t &completed_count;
        size_t expected_size;

        void set_value(
            monad::async::erased_connected_operation *,
            monad::async::read_single_buffer_sender::result_type r)
        {
            MONAD_ASSERT(r);
            EXPECT_EQ(r.assume_value().get().size(), expected_size);
            completed_count++;
        }
    };

    TEST(AsyncIO, concurrent_read_io_limit_defers_and_completes_reads)
    {
        monad::async::storage_pool pool(
            monad::async::use_anonymous_inode_tag{});

        {
            auto chunk = pool.chunk(pool.seq, 0);
            auto const fd = chunk.write_fd(monad::async::DISK_PAGE_SIZE);
            std::vector<char> data(monad::async::DISK_PAGE_SIZE, 'A');
            MONAD_ASSERT(
                -1 != ::pwrite(
                          fd.first,
                          data.data(),
                          monad::async::DISK_PAGE_SIZE,
                          static_cast<off_t>(fd.second)));
        }

        monad::io::Ring testring;
        monad::io::Buffers testrwbuf = monad::io::make_buffers_for_read_only(
            testring, 10, monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE);
        monad::async::AsyncIO testio(pool, testrwbuf);

        testio.set_concurrent_read_io_limit(2);
        EXPECT_EQ(testio.concurrent_read_io_limit(), 2u);

        size_t completed = 0;
        constexpr size_t NUM_READS = 10;

        // Issue NUM_READS concurrent reads, but only 2 can be in flight at once
        for (size_t n = 0; n < NUM_READS; n++) {
            auto state = testio.make_connected(
                monad::async::read_single_buffer_sender(
                    {0, 0}, monad::async::DISK_PAGE_SIZE),
                concurrent_read_limit_receiver{
                    completed, monad::async::DISK_PAGE_SIZE});

            state->initiate();
            (void)state.release();
        }

        testio.wait_until_done();

        EXPECT_LE(testio.max_reads_in_flight(), 2u);

        EXPECT_EQ(completed, NUM_READS);
        EXPECT_EQ(testio.reads_in_flight(), 0u);
    }
}
