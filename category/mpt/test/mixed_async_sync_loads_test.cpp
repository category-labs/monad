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
#include <category/async/erased_connected_operation.hpp>
#include <category/mpt/find_request_sender.hpp>

#include <category/mpt/node.hpp>
#include <category/mpt/trie.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <iostream>
#include <ostream>

struct MixedAsyncSyncLoadsTest
    : public monad::test::FillDBWithChunksGTest<
          monad::test::FillDBWithChunksConfig{.chunks_to_fill = 1}>
{
};

TEST_F(MixedAsyncSyncLoadsTest, works)
{
    // Make a new empty DB
    monad::test::UpdateAux<void> aux{&state()->io};
    monad::test::StateMachineAlwaysMerkle sm;
    // Load its root
    auto const latest_version = aux.db_history_max_version();
    monad::mpt::Node::UniquePtr root{monad::mpt::read_node_blocking(
        aux, aux.get_root_offset_at_version(latest_version), latest_version)};
    auto const &key = state()->keys.front().first;
    auto const &value = state()->keys.front().first;

    struct receiver_t
    {
        std::optional<
            monad::mpt::find_request_sender<>::result_type::value_type>
            res;

        enum : bool
        {
            lifetime_managed_internally = false
        };

        void set_value(
            monad::async::erased_connected_operation *,
            monad::mpt::find_request_sender<>::result_type r)
        {
            MONAD_ASSERT(r);
            res = std::move(r).assume_value();
        }
    };

    // Initiate an async find of a key
    monad::mpt::inflight_node_t inflights;
    auto state = monad::async::connect(
        monad::mpt::find_request_sender<>(aux, inflights, *root, key, true, 5),
        receiver_t{});
    state.initiate();

    // Synchronously load the same key
    EXPECT_EQ(
        find_blocking(aux, *root, key, latest_version).first.node->value(),
        value);

    // Let the async find of that key complete
    while (!state.receiver().res) {
        aux.io->poll_blocking();
    }
    EXPECT_EQ(state.receiver().res->first, value);
}
