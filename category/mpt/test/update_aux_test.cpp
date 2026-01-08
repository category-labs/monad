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

#include <category/async/config.hpp>
#include <category/async/io.hpp>
#include <category/async/storage_pool.hpp>
#include <category/async/util.hpp>
#include <category/core/assert.h>
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>
#include <category/mpt/detail/db_metadata.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/util.hpp>

#include <gtest/gtest.h>

#include <atomic>
#include <bits/chrono.h>
#include <csignal>
#include <cstdint>
#include <filesystem>
#include <span>
#include <stdlib.h>
#include <stop_token>
#include <thread>
#include <unistd.h>

using namespace std::chrono_literals;

namespace
{
    constexpr uint64_t AUX_TEST_HISTORY_LENGTH = 1000;
}

TEST(update_aux_test, set_io_reader_dirty)
{
    monad::async::storage_pool pool(monad::async::use_anonymous_inode_tag{});

    // All this threading nonsense is because we can't have two AsyncIO
    // instances on the same thread.

    monad::mpt::UpdateAux aux_writer{};
    std::atomic<bool> io_set = false;
    std::jthread const rw_asyncio([&](std::stop_token token) {
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers testbuf =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testbuf);
        aux_writer.set_io(testio, AUX_TEST_HISTORY_LENGTH);
        io_set = true;

        while (!token.stop_requested()) {
            std::this_thread::sleep_for(10ms);
        }
        aux_writer.unset_io();
    });
    while (!io_set) {
        std::this_thread::yield();
    }

    // Set both bits dirty
    aux_writer.modify_metadata([](monad::mpt::detail::db_metadata *m) {
        m->is_dirty().store(1, std::memory_order_release);
    });

    ASSERT_TRUE(
        const_cast<monad::mpt::detail::db_metadata *>(aux_writer.db_metadata())
            ->is_dirty());

    struct TestAux : public monad::mpt::UpdateAuxImpl
    {
        monad::mpt::UpdateAux<> &write_aux;
        bool was_dirty{false};

        explicit TestAux(monad::mpt::UpdateAux<> &write_aux_)
            : write_aux(write_aux_)
        {
        }

        void lock_unique_() const override {}

        void unlock_unique_() const noexcept override {}

        void lock_shared_() const override {}

        void unlock_shared_() const noexcept override {}

        bool upgrade_shared_to_unique_() const noexcept override
        {
            return true;
        }

        bool downgrade_unique_to_shared_() const noexcept override
        {
            return true;
        }

        void on_read_only_init_with_dirty_bit() noexcept override
        {
            was_dirty = true;

            // Disable the dirty bits. This simulates the writer unsetting dirty
            // bit.
            write_aux.modify_metadata([](monad::mpt::detail::db_metadata *m) {
                m->is_dirty().store(0, std::memory_order_release);
            });
        }
    };

    monad::io::Ring ring;
    monad::io::Buffers testrobuf = monad::io::make_buffers_for_read_only(
        ring, 2, monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE);
    auto pool_ro = pool.clone_as_read_only();
    monad::async::AsyncIO testio(pool_ro, testrobuf);

    // This should throw. Dirty bit stays set.
    ASSERT_DEATH(
        ({
            monad::mpt::UpdateAux<> aux_reader{};
            aux_reader.set_io(testio, AUX_TEST_HISTORY_LENGTH);
        }),
        "DB metadata was closed dirty, but not opened for healing");

    // TestAux adds instrumentation to turn off the dirty bit. Should not throw.
    TestAux aux_reader(aux_writer);
    EXPECT_NO_THROW(aux_reader.set_io(testio, AUX_TEST_HISTORY_LENGTH));
    EXPECT_TRUE(aux_reader.was_dirty) << "target codepath not exercised";
}

TEST(update_aux_test, root_offsets_fast_slow)
{
    testing::FLAGS_gtest_death_test_style = "threadsafe";

    monad::async::storage_pool pool(monad::async::use_anonymous_inode_tag{});
    monad::io::Ring ring1;
    monad::io::Ring ring2;
    monad::io::Buffers testbuf =
        monad::io::make_buffers_for_segregated_read_write(
            ring1,
            ring2,
            2,
            4,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
    monad::async::AsyncIO testio(pool, testbuf);
    {
        monad::mpt::UpdateAux aux_writer{};
        aux_writer.set_io(testio, AUX_TEST_HISTORY_LENGTH);

        // Root offset at 0, fast list offset at 50. This is correct
        auto const start_offset =
            aux_writer.node_writer_fast->sender().offset();
        (void)pool
            .chunk(monad::async::storage_pool::chunk_type::seq, start_offset.id)
            .write_fd(50);
        auto const end_offset =
            aux_writer.node_writer_fast->sender().offset().add_to_offset(50);
        aux_writer.append_root_offset(start_offset);
        aux_writer.advance_db_offsets_to(
            end_offset, aux_writer.node_writer_slow->sender().offset());
    }
    {
        // verify set_io() succeeds
        monad::mpt::UpdateAux aux_writer{};
        aux_writer.set_io(testio, AUX_TEST_HISTORY_LENGTH);
        EXPECT_EQ(aux_writer.root_offsets().max_version(), 0);

        // Write version 1. However, append the new root offset without
        // advancing fast list
        auto const start_offset =
            aux_writer.node_writer_fast->sender().offset();
        (void)pool
            .chunk(monad::async::storage_pool::chunk_type::seq, start_offset.id)
            .write_fd(100);
        auto const end_offset =
            aux_writer.node_writer_fast->sender().offset().add_to_offset(100);
        aux_writer.append_root_offset(end_offset);
    }

    { // Fail to reopen upon calling rewind_to_match_offsets()
        monad::mpt::UpdateAux aux_writer{};
        EXPECT_EXIT(
            aux_writer.set_io(testio, AUX_TEST_HISTORY_LENGTH),
            ::testing::KilledBySignal(SIGABRT),
            "Detected corruption");
    }
}

TEST(update_aux_test, configurable_root_offset_chunks)
{
    std::filesystem::path const filename{
        MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
        "monad_update_aux_test_XXXXXX"};
    int const fd = ::mkstemp((char *)filename.native().data());
    MONAD_ASSERT(fd != -1);
    MONAD_ASSERT(-1 != ::ftruncate(fd, 8UL << 30)); // 8GB

    monad::io::Ring ring1;
    monad::io::Ring ring2;
    monad::io::Buffers testbuf =
        monad::io::make_buffers_for_segregated_read_write(
            ring1,
            ring2,
            2,
            4,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
    monad::async::storage_pool::creation_flags flags;
    flags.num_cnv_chunks = 5;
    {
        // Create storage pool with 5 conventional chunks
        monad::async::storage_pool pool(
            std::span{&filename, 1},
            monad::async::storage_pool::mode::truncate,
            flags);
        EXPECT_EQ(pool.chunks(monad::async::storage_pool::cnv), 5);

        monad::async::AsyncIO testio(pool, testbuf);
        monad::mpt::UpdateAux<> const aux(testio);

        // Verify that exactly 4 chunks were allocated to hold two copies of
        // root offsets, since chunk 0 is used for metadata
        EXPECT_EQ(aux.db_metadata()->root_offsets.storage_.cnv_chunks_len, 4);
        EXPECT_EQ(aux.root_offsets().capacity(), 2ULL << 25);
    }
    {
        // reopen storage_pool
        monad::async::storage_pool pool(
            std::span{&filename, 1},
            monad::async::storage_pool::mode::open_existing,
            flags);
        EXPECT_EQ(pool.chunks(monad::async::storage_pool::cnv), 5);
        monad::async::AsyncIO testio(pool, testbuf);
        monad::mpt::UpdateAux<> const aux(testio);
        EXPECT_EQ(aux.db_metadata()->root_offsets.storage_.cnv_chunks_len, 4);
        EXPECT_EQ(aux.root_offsets().capacity(), 2ULL << 25);
    }
    remove(filename);
}
