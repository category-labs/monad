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

#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include "fuzz/one_hundred_updates.hpp"

#include <category/async/config.hpp>
#include <category/async/io.hpp>
#include <category/core/byte_string.hpp>
#include <category/mpt/detail/boost_fiber_workarounds.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/update.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

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
        UpdateAuxImpl *aux, inflight_map_t *const inflights,
        Node::SharedPtr root, monad::byte_string_view const key,
        monad::byte_string_view const value)
    {
        monad::threadsafe_boost_fibers_promise<
            monad::mpt::find_cursor_result_type>
            promise;
        find_notify_fiber_future(
            *aux, *inflights, promise, NodeCursor{root}, key);
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
            0xcbb6d81afdc76fec144f6a1a283205d42c03c102a94fc210b3a1bcfdcb625884_bytes);

        inflight_map_t inflights;
        boost::fibers::fiber find_fiber(
            find,
            &this->aux,
            &inflights,
            root,
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
            0xcbb6d81afdc76fec144f6a1a283205d42c03c102a94fc210b3a1bcfdcb625884_bytes);

        inflight_map_t inflights;
        std::vector<boost::fibers::fiber> fibers;
        for (auto const &[key, val] : one_hundred_updates) {
            fibers.emplace_back(find, &this->aux, &inflights, root, key, val);
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
