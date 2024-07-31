#include "gtest/gtest.h"

#include <chrono>
#include <thread>

#include <monad/async/config.hpp>
#include <monad/async/detail/scope_polyfill.hpp>
#include <monad/async/io.hpp>
#include <monad/async/storage_pool.hpp>
#include <monad/async/util.hpp>
#include <monad/io/buffers.hpp>
#include <monad/io/config.hpp>
#include <monad/io/ring.hpp>
#include <monad/mpt/detail/db_metadata.hpp>
#include <monad/mpt/trie.hpp>

using namespace std::chrono_literals;

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
        aux_writer.set_io(&testio);
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
    EXPECT_THROW(aux_reader_throw.set_io(&testio), std::runtime_error);

    // TestAux adds instrumentation to turn off the dirty bit. Should not throw.
    TestAux aux_reader(aux_writer);
    EXPECT_NO_THROW(aux_reader.set_io(&testio));
    EXPECT_TRUE(aux_reader.was_dirty) << "target codepath not exercised";
}
