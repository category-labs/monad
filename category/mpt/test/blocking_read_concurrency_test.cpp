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

#include "test_fixtures_gtest.hpp"

#include <category/async/io.hpp>
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/trie.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <chrono>
#include <condition_variable>
#include <future>
#include <ostream>
#include <thread>

using namespace MONAD_ASYNC_NAMESPACE;
using namespace MONAD_MPT_NAMESPACE;

namespace
{
    struct DummyTraverseMachine : public TraverseMachine
    {
        Nibbles path{};

        virtual bool down(unsigned char branch, Node const &node) override
        {
            if (branch == INVALID_BRANCH) {
                return true;
            }
            path = concat(NibblesView{path}, branch, node.path_nibble_view());

            if (node.has_value()) {
                MONAD_ASSERT(path.nibble_size() == KECCAK256_SIZE * 2);
            }
            return true;
        }

        virtual void up(unsigned char branch, Node const &node) override
        {
            auto const path_view = NibblesView{path};
            auto const rem_size = [&] {
                if (branch == INVALID_BRANCH) {
                    MONAD_ASSERT(path_view.nibble_size() == 0);
                    return 0;
                }
                int const rem_size = path_view.nibble_size() - 1 -
                                     node.path_nibble_view().nibble_size();
                MONAD_ASSERT(rem_size >= 0);
                MONAD_ASSERT(
                    path_view.substr(static_cast<unsigned>(rem_size)) ==
                    concat(branch, node.path_nibble_view()));
                return rem_size;
            }();
            path = path_view.substr(0, static_cast<unsigned>(rem_size));
        }

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<DummyTraverseMachine>(*this);
        }
    };
}

struct DbConcurrencyTest1
    : public monad::test::FillDBWithChunksGTest<
          monad::test::FillDBWithChunksConfig{.chunks_to_fill = 1}>
{
};

TEST_F(DbConcurrencyTest1, version_outdated_during_blocking_find)
{
    // Load root of most recent version
    auto const latest_version = state()->aux.db_history_max_version();
    Node::SharedPtr root = read_node_blocking(
        state()->aux,
        state()->aux.get_root_offset_at_version(latest_version),
        latest_version);
    ASSERT_TRUE(root);
    auto const &key = state()->keys.front().first;
    auto const &value = state()->keys.front().first;

    // Create a promise/future pair to track completion
    std::promise<int> completion_promise;
    std::future<int> completion_future = completion_promise.get_future();
    std::mutex lock;
    std::condition_variable cond;

    auto find_loop = [&](std::stop_token const stop_token) {
        // Read only aux
        auto pool = state()->pool.clone_as_read_only();
        monad::io::Ring ring{monad::io::RingConfig{2}};
        monad::io::Buffers rwbuf{monad::io::make_buffers_for_read_only(
            ring, 2, AsyncIO::MONAD_IO_BUFFERS_READ_SIZE)};
        AsyncIO io{pool, rwbuf};
        monad::test::UpdateAux<void> ro_aux{&io};

        int count = 0;
        while (!stop_token.stop_requested()) {
            // clear all in memory nodes under root
            for (unsigned idx = 0; idx < root->number_of_children(); ++idx) {
                root->move_next(idx).reset();
            }
            auto [node_cursor, res] =
                find_blocking(ro_aux, NodeCursor{root}, key, latest_version);
            if (res != find_result::success) {
                ASSERT_EQ(res, find_result::version_no_longer_exist);
                completion_promise.set_value(count);
                return;
            }

            EXPECT_EQ(node_cursor.node->value(), value);
            ++count;
            if (count == 1) {
                std::unique_lock g(lock);
                cond.notify_one();
            }
        }
    };

    std::jthread reader{find_loop};

    // Erase the version when the first read finishes
    {
        std::unique_lock g(lock);
        cond.wait(g);
    }
    // Erase the version being read should trigger a find failure and ends the
    // reader thread
    state()->aux.update_root_offset(latest_version, INVALID_OFFSET);
    EXPECT_FALSE(state()->aux.version_is_valid_ondisk(latest_version));

    // Wait for completion with timeout
    auto const status = completion_future.wait_for(std::chrono::seconds(5));
    ASSERT_NE(status, std::future_status::timeout)
        << "Test Failure: find loop timeout. Find loop is expected to "
        << "end with an unsuccessful find immediately after latest "
        << "version is erased by main thread.";
    int const nfinished_finds = completion_future.get();
    EXPECT_GT(nfinished_finds, 0);
    std::cout << "Did " << nfinished_finds << " successful finds at version "
              << latest_version << " before it gets erased." << std::endl;
}

struct DbConcurrencyTest2
    : public monad::test::FillDBWithChunksGTest<
          monad::test::FillDBWithChunksConfig{.chunks_to_fill = 1}>
{
};

TEST_F(DbConcurrencyTest2, version_outdated_during_blocking_traverse)
{
    // Load root of most recent version
    auto const latest_version = state()->aux.db_history_max_version();
    Node::SharedPtr root = read_node_blocking(
        state()->aux,
        state()->aux.get_root_offset_at_version(latest_version),
        latest_version);
    ASSERT_TRUE(root);

    // Create a promise/future pair to track completion
    std::promise<int> completion_promise;
    std::future<int> completion_future = completion_promise.get_future();
    std::mutex lock;
    std::condition_variable cond;

    auto traverse_loop = [&](std::stop_token const stop_token) {
        // Read only aux
        auto pool = state()->pool.clone_as_read_only();
        monad::io::Ring ring{monad::io::RingConfig{2}};
        monad::io::Buffers rwbuf{monad::io::make_buffers_for_read_only(
            ring, 2, AsyncIO::MONAD_IO_BUFFERS_READ_SIZE)};
        AsyncIO io{pool, rwbuf};
        monad::test::UpdateAux<void> ro_aux{&io};

        DummyTraverseMachine traverse{};
        int count = 0;
        while (!stop_token.stop_requested()) {
            if (!preorder_traverse_blocking(
                    ro_aux, *root, traverse, latest_version)) {
                std::cout << "Traverse loop ends due to version being erased "
                             "from history on disk."
                          << std::endl;
                completion_promise.set_value(count);
                return;
            }
            ++count;
            if (count == 1) {
                std::unique_lock g(lock);
                cond.notify_one();
            }
        }
    };

    std::jthread reader{traverse_loop};
    // Erase the version when the first traverse finishes
    {
        std::unique_lock g(lock);
        cond.wait(g);
    }
    // Erase the version being read should stop traverse in the reader thread
    state()->aux.update_root_offset(latest_version, INVALID_OFFSET);
    EXPECT_FALSE(state()->aux.version_is_valid_ondisk(latest_version));

    // Wait for completion with timeout
    auto const status = completion_future.wait_for(std::chrono::seconds(5));
    ASSERT_NE(status, std::future_status::timeout)
        << "Test Failure: traverse loop timeout. Traverse loop is expected to "
        << "end with an unsuccessful find immediately after latest "
        << "version is erased by main thread.";
    int const nfinished_traversals = completion_future.get();
    EXPECT_GT(nfinished_traversals, 0);
    std::cout << "Did " << nfinished_traversals
              << " successful traversals at version " << latest_version
              << " before it gets erased." << std::endl;
}
