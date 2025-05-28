#include "gtest/gtest.h"

#include <chrono>
#include <thread>

#include <monad/async/config.hpp>
#include <monad/async/io.hpp>
#include <monad/async/storage_pool.hpp>
#include <monad/async/util.hpp>
#include <monad/core/scope_polyfill.hpp>
#include <monad/io/buffers.hpp>
#include <monad/io/config.hpp>
#include <monad/io/ring.hpp>
#include <monad/mpt/detail/db_metadata.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/util.hpp>

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
    std::jthread rw_asyncio([&](std::stop_token token) {
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
        aux_writer.set_io(&testio, AUX_TEST_HISTORY_LENGTH);
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

        TestAux(monad::mpt::UpdateAux<> &write_aux_)
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
    monad::mpt::UpdateAux<> aux_reader_throw{};
    EXPECT_THROW(
        aux_reader_throw.set_io(&testio, AUX_TEST_HISTORY_LENGTH),
        std::runtime_error);

    // TestAux adds instrumentation to turn off the dirty bit. Should not throw.
    TestAux aux_reader(aux_writer);
    EXPECT_NO_THROW(aux_reader.set_io(&testio, AUX_TEST_HISTORY_LENGTH));
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
        aux_writer.set_io(&testio, AUX_TEST_HISTORY_LENGTH);

        // Root offset at 0, fast list offset at 50. This is correct
        auto const start_offset =
            aux_writer.node_writer_fast->sender().offset();
        (void)pool
            .chunk(monad::async::storage_pool::chunk_type::seq, start_offset.id)
            ->write_fd(50);
        auto const end_offset =
            aux_writer.node_writer_fast->sender().offset().add_to_offset(50);
        aux_writer.append_root_offset(start_offset);
        aux_writer.advance_db_offsets_to(
            end_offset, aux_writer.node_writer_slow->sender().offset());
    }
    {
        // verify set_io() succeeds
        monad::mpt::UpdateAux aux_writer{};
        aux_writer.set_io(&testio, AUX_TEST_HISTORY_LENGTH);
        EXPECT_EQ(aux_writer.root_offsets().max_version(), 0);

        // Write version 1. However, append the new root offset without
        // advancing fast list
        auto const start_offset =
            aux_writer.node_writer_fast->sender().offset();
        (void)pool
            .chunk(monad::async::storage_pool::chunk_type::seq, start_offset.id)
            ->write_fd(100);
        auto const end_offset =
            aux_writer.node_writer_fast->sender().offset().add_to_offset(100);
        aux_writer.append_root_offset(end_offset);
    }

    { // Fail to reopen upon calling rewind_to_match_offsets()
        monad::mpt::UpdateAux aux_writer{};
        EXPECT_EXIT(
            aux_writer.set_io(&testio, AUX_TEST_HISTORY_LENGTH),
            ::testing::KilledBySignal(SIGABRT),
            "Detected corruption");
    }
}
