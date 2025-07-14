#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include "fuzz/one_hundred_updates.hpp"

#include <category/async/config.hpp>
#include <category/async/io.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/hex_literal.hpp>
#include <monad/mpt/detail/boost_fiber_workarounds.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/update.hpp>

#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <boost/fiber/fiber.hpp>
#include <boost/fiber/operations.hpp>

#include <chrono>
#include <utility>
#include <vector>

namespace
{
    using namespace monad::test;
    using namespace MONAD_ASYNC_NAMESPACE;

    void find(
        UpdateAuxImpl *aux, inflight_map_t *const inflights, Node *const root,
        monad::byte_string_view const key, monad::byte_string_view const value)
    {
        monad::threadsafe_boost_fibers_promise<
            monad::mpt::find_cursor_result_type>
            promise;
        find_notify_fiber_future(
            *aux, *inflights, promise, NodeCursor{*root}, key);
        auto const [it, errc] = promise.get_future().get();
        ASSERT_TRUE(it.is_valid());
        EXPECT_EQ(errc, monad::mpt::find_result::success);
        EXPECT_EQ(it.node->value(), value);
    };

    void poll(AsyncIO *const io, bool *signal_done)
    {
        while (!*signal_done) {
            io->poll_nonblocking(1);
            boost::this_fiber::sleep_for(std::chrono::milliseconds(1));
        }
    };

    TEST_F(OnDiskMerkleTrieGTest, single_thread_one_find_fiber)
    {
        std::vector<Update> updates;
        for (auto const &i : one_hundred_updates) {
            updates.emplace_back(make_update(i.first, i.second));
        }
        this->root = upsert_vector(
            this->aux, *this->sm, std::move(this->root), std::move(updates));
        EXPECT_EQ(
            root_hash(),
            0xcbb6d81afdc76fec144f6a1a283205d42c03c102a94fc210b3a1bcfdcb625884_hex);

        inflight_map_t inflights;
        boost::fibers::fiber find_fiber(
            find,
            &this->aux,
            &inflights,
            root.get(),
            one_hundred_updates[0].first,
            one_hundred_updates[0].second);
        bool signal_done = false;
        boost::fibers::fiber poll_fiber(poll, aux.io, &signal_done);
        find_fiber.join();
        signal_done = true;
        poll_fiber.join();
    }

    TEST_F(OnDiskMerkleTrieGTest, single_thread_one_hundred_find_fibers)
    {
        std::vector<Update> updates;
        for (auto const &i : one_hundred_updates) {
            updates.emplace_back(make_update(i.first, i.second));
        }
        this->root = upsert_vector(
            this->aux, *this->sm, std::move(this->root), std::move(updates));
        EXPECT_EQ(
            root_hash(),
            0xcbb6d81afdc76fec144f6a1a283205d42c03c102a94fc210b3a1bcfdcb625884_hex);

        inflight_map_t inflights;
        std::vector<boost::fibers::fiber> fibers;
        for (auto const &[key, val] : one_hundred_updates) {
            fibers.emplace_back(
                find, &this->aux, &inflights, root.get(), key, val);
        }

        bool signal_done = false;
        boost::fibers::fiber poll_fiber(poll, aux.io, &signal_done);

        for (auto &fiber : fibers) {
            fiber.join();
        }
        signal_done = true;
        poll_fiber.join();
    }
}
