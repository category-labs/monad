#include "monad/mpt/find_request_sender.hpp"
#include "test_fixtures_gtest.hpp"
#include <category/async/erased_connected_operation.hpp>

#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>

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
