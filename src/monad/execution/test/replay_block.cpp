#include <gtest/gtest.h>

#include <monad/config.hpp>

#include <monad/execution/replay_block.hpp>

#include <monad/execution/block_processor_interface.hpp>
#include <monad/execution/config.hpp>
#include <monad/execution/execution_model.hpp>
#include <monad/execution/test/fakes.hpp>
#include <monad/execution/transaction_processor.hpp>
#include <monad/execution/transaction_processor_data.hpp>

MONAD_NAMESPACE_BEGIN

namespace db::fake
{
    class BlockDb : IBlockDb
    {
    public:
        block_num_t block_number_threshold;

        bool
        get([[maybe_unused]] block_num_t block_number,
            [[maybe_unused]] Block &block) const override
        {
            if (block_number < block_number_threshold) {
                return true;
            }
            else {
                return false;
            }
        }
    };
}

namespace execution::fake
{
    class BlockProcessor final
        : public execution::IBlockProcessor<execution::BoostFiberExecution>
    {
    public:
        template <
            concepts::fork_traits<execution::fake::State> TTraits,
            class TFiberData>
        std::vector<Receipt> execute(
            [[maybe_unused]] const Block &block,
            [[maybe_unused]] execution::fake::State &state)
        {
            return {};
        }
    };
}

namespace trie::fake
{
    class StateTrie final : public trie::IStateTrie<execution::fake::State>
    {
    public:
        void incremental_update(
            [[maybe_unused]] execution::fake::State &state) override
        {
            return;
        }
    };
}

using state_t = execution::fake::State;
using traits_t = execution::fake::traits<state_t>;
using block_db_t = db::fake::BlockDb;
using block_processor_t = execution::fake::BlockProcessor;
using state_trie_t = trie::fake::StateTrie;

using replay_block_t = execution::ReplayBlock<
    state_t, block_db_t, block_processor_t, state_trie_t,
    execution::BoostFiberExecution>;

TEST(ReplayBlock, start_block_number_outside_db)
{
    block_db_t block_db;
    block_db.block_number_threshold = 0u;
    state_t state;
    replay_block_t replay_block;
    auto [status, finished_block_number] = replay_block.run(state, block_db, 0);
    EXPECT_EQ(status, replay_block_t::Status::START_BLOCK_NUMBER_OUTSIDE_DB);
    EXPECT_EQ(finished_block_number, 0u);
}

TEST(ReplayBlock, invalid_end_block_number)
{
    block_db_t block_db;
    block_db.block_number_threshold = 1'000u;
    state_t state;
    replay_block_t replay_block;
    auto [status, finished_block_number] =
        replay_block.run(state, block_db, 100, 100);
    EXPECT_EQ(status, replay_block_t::Status::INVALID_END_BLOCK_NUMBER);
    EXPECT_EQ(finished_block_number, 0u);
}

TEST(ReplayBlock, invalid_end_block_number_zero)
{
    block_db_t block_db;
    block_db.block_number_threshold = 1'000u;
    state_t state;
    replay_block_t replay_block;
    auto [status, finished_block_number] =
        replay_block.run(state, block_db, 0u, 0u);
    EXPECT_EQ(status, replay_block_t::Status::INVALID_END_BLOCK_NUMBER);
    EXPECT_EQ(finished_block_number, 0u);
}

TEST(ReplayBlock, one_block)
{
    block_db_t block_db;
    block_db.block_number_threshold = 1'000u;
    state_t state;
    replay_block_t replay_block;
    auto [status, finished_block_number] =
        replay_block.run(state, block_db, 100, 101);
    EXPECT_EQ(status, replay_block_t::Status::COMPLETE);
    EXPECT_EQ(finished_block_number, 100u);
}

TEST(ReplayBlock, frontier_run_from_zero)
{
    block_db_t block_db;
    block_db.block_number_threshold = 1'234u;
    state_t state;
    replay_block_t replay_block;
    auto [status, finished_block_number] = replay_block.run(state, block_db, 0);
    EXPECT_EQ(status, replay_block_t::Status::END_OF_BLOCKDB);
    EXPECT_EQ(finished_block_number, 1'233u);
}

TEST(ReplayBlock, frontier_to_homestead)
{
    block_db_t block_db;
    block_db.block_number_threshold =
        fork_traits::frontier::last_block_number + 10;
    state_t state;
    replay_block_t replay_block;
    auto [status, finished_block_number] = replay_block.run(
        state, block_db, fork_traits::frontier::last_block_number - 10);
    EXPECT_EQ(status, replay_block_t::Status::END_OF_BLOCKDB);
    EXPECT_EQ(finished_block_number, 1'150'008u);
}

TEST(ReplayBlock, berlin_to_london)
{
    block_db_t block_db;
    block_db.block_number_threshold =
        fork_traits::berlin::last_block_number + 10;
    state_t state;
    replay_block_t replay_block;
    auto [status, finished_block_number] = replay_block.run(
        state, block_db, fork_traits::berlin::last_block_number - 10);
    EXPECT_EQ(status, replay_block_t::Status::END_OF_BLOCKDB);
    EXPECT_EQ(finished_block_number, 12'965'008u);
}

TEST(ReplayBlock, frontier_to_spurious_dragon)
{
    block_db_t block_db;
    block_db.block_number_threshold =
        fork_traits::homestead::last_block_number + 20;
    state_t state;
    replay_block_t replay_block;
    auto [status, finished_block_number] = replay_block.run(
        state, block_db, fork_traits::frontier::last_block_number - 10);
    EXPECT_EQ(status, replay_block_t::Status::END_OF_BLOCKDB);
    EXPECT_EQ(finished_block_number, 2'675'018u);
}

MONAD_NAMESPACE_END