#include <monad/execution/block_processor.hpp>
#include <monad/execution/config.hpp>
#include <monad/execution/execution_model.hpp>

#include <monad/execution/stats/stats.hpp>
#include <monad/execution/stats/stats_writer.hpp>

#include <monad/execution/test/fakes.hpp>

#include <boost/fiber/all.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::execution;

using state_t = fake::State;
using stats_collector_t = std::vector<stats::BlockStats>;

template <class TState, class TStatsWriter>
struct fakeStartStopFiberData
{
    int _id{};
    stats::BlockStats &_block_stats;
    fakeStartStopFiberData(
        TState &, Transaction const &, BlockHeader const &, int id,
        stats::BlockStats &bs)
        : _id(id)
        , _block_stats(bs)
    {
    }
    inline void operator()()
    {
        TStatsWriter::start_txn(_block_stats, static_cast<size_t>(_id));
        TStatsWriter::finish_txn(_block_stats, static_cast<size_t>(_id));
    }
};

template <class TState, class TStatsWriter, class TExecution>
struct fakeRestartFiberData
{
    int _id{};
    stats::BlockStats &_block_stats;
    fakeRestartFiberData(
        TState &, Transaction const &, BlockHeader const &, int id,
        stats::BlockStats &bs)
        : _id(id)
        , _block_stats(bs)
    {
    }
    inline void operator()()
    {
        TStatsWriter::start_txn(_block_stats, static_cast<size_t>(_id));

        // selective restart
        if (_id == 1u) {
            TExecution::yield();
            std::this_thread::sleep_for(std::chrono::seconds(1));
            TStatsWriter::start_txn(_block_stats, static_cast<size_t>(_id));
        }

        TStatsWriter::finish_txn(_block_stats, static_cast<size_t>(_id));
    }
};

template <class TExecution>
struct fakeStatsBP
{
    template <
        class TState, class TFiberData, class TStatsCollector,
        class TStatsWriter>
    [[nodiscard]] std::vector<Receipt>
    execute(TState &s, Block const &b, TStatsCollector &stats_collector)
    {
        std::vector<TFiberData> data{};
        std::vector<typename TExecution::fiber_t> fibers{};

        stats::BlockStats block_stats(b);
        TStatsWriter::start_block(block_stats);

        int i = 0;
        for (auto const &txn : b.transactions) {
            data.push_back({s, txn, b.header, i, block_stats});
            fibers.emplace_back(data.back());
            ++i;
        }
        TExecution::yield();

        for (auto &fiber : fibers) {
            fiber.join();
        }

        TStatsWriter::finish_block(block_stats);
        stats_collector.emplace_back(block_stats);

        return {};
    }
};

TEST(Stats, empty_block)
{
    using block_processor_t = fakeStatsBP<BoostFiberExecution>;
    using fiber_data_t = fakeStartStopFiberData<state_t, stats::StatsWriter>;

    fake::State s{};
    stats_collector_t stats_collector;
    static Block const b{
        .header = {},
    };

    block_processor_t p{};
    [[maybe_unused]] auto const r =
        p.execute<state_t, fiber_data_t, stats_collector_t, stats::StatsWriter>(
            s, b, stats_collector);

    EXPECT_EQ(stats_collector.size(), 1u);
    EXPECT_EQ(stats_collector[0].finished_txns_.size(), 0u);
    EXPECT_EQ(stats_collector[0].running_txns_.size(), 0u);
    EXPECT_GT(
        stats_collector[0].finished_time_, stats_collector[0].start_time_);
}

TEST(Stats, one_txn)
{
    using block_processor_t = fakeStatsBP<BoostFiberExecution>;
    using fiber_data_t = fakeStartStopFiberData<state_t, stats::StatsWriter>;

    fake::State s{};
    stats_collector_t stats_collector;
    static Block const b{.header = {}, .transactions = {{}}};

    block_processor_t p{};
    [[maybe_unused]] auto const r =
        p.execute<state_t, fiber_data_t, stats_collector_t, stats::StatsWriter>(
            s, b, stats_collector);

    EXPECT_EQ(stats_collector.size(), 1u);
    EXPECT_EQ(stats_collector[0].finished_txns_.size(), 1u);
    EXPECT_EQ(stats_collector[0].running_txns_.size(), 0u);

    // block.start < txn.start < txn.finish < block.finish
    EXPECT_GT(
        stats_collector[0].finished_time_, stats_collector[0].start_time_);
    EXPECT_GT(
        stats_collector[0].finished_txns_[0].finished_time_,
        stats_collector[0].finished_txns_[0].start_time_);
    EXPECT_GT(
        stats_collector[0].finished_time_,
        stats_collector[0].finished_txns_[0].finished_time_);
    EXPECT_GT(
        stats_collector[0].finished_txns_[0].start_time_,
        stats_collector[0].start_time_);
}

TEST(Stats, many_txns)
{
    using block_processor_t = fakeStatsBP<BoostFiberExecution>;
    using fiber_data_t = fakeStartStopFiberData<state_t, stats::StatsWriter>;

    fake::State s{};
    stats_collector_t stats_collector;
    static Block const b{.header = {}, .transactions = {{}, {}, {}}};

    block_processor_t p{};
    [[maybe_unused]] auto const r =
        p.execute<state_t, fiber_data_t, stats_collector_t, stats::StatsWriter>(
            s, b, stats_collector);

    EXPECT_EQ(stats_collector.size(), 1u);
    EXPECT_EQ(stats_collector[0].finished_txns_.size(), 3u);
    EXPECT_EQ(stats_collector[0].running_txns_.size(), 0u);

    // block.start < txn.start < ... <  txn.finish < block.finish
    EXPECT_GT(
        stats_collector[0].finished_txns_[0].start_time_,
        stats_collector[0].start_time_);
    EXPECT_GT(
        stats_collector[0].finished_txns_[0].finished_time_,
        stats_collector[0].finished_txns_[0].start_time_);
    EXPECT_GT(
        stats_collector[0].finished_txns_[1].start_time_,
        stats_collector[0].finished_txns_[0].start_time_);
    EXPECT_GT(
        stats_collector[0].finished_txns_[1].finished_time_,
        stats_collector[0].finished_txns_[1].start_time_);
    EXPECT_GT(
        stats_collector[0].finished_txns_[2].start_time_,
        stats_collector[0].finished_txns_[1].start_time_);
    EXPECT_GT(
        stats_collector[0].finished_txns_[2].finished_time_,
        stats_collector[0].finished_txns_[2].start_time_);
    EXPECT_GT(
        stats_collector[0].finished_time_,
        stats_collector[0].finished_txns_[2].finished_time_);
}

TEST(Stats, restart_txn)
{
    using block_processor_t = fakeStatsBP<BoostFiberExecution>;
    using fiber_data_t =
        fakeRestartFiberData<state_t, stats::StatsWriter, BoostFiberExecution>;

    fake::State s{};
    stats_collector_t stats_collector;
    static Block const b{.header = {}, .transactions = {{}, {}, {}}};

    block_processor_t p{};
    [[maybe_unused]] auto const r =
        p.execute<state_t, fiber_data_t, stats_collector_t, stats::StatsWriter>(
            s, b, stats_collector);

    EXPECT_EQ(stats_collector.size(), 1u);
    EXPECT_EQ(stats_collector[0].finished_txns_.size(), 3u);
    EXPECT_EQ(stats_collector[0].running_txns_.size(), 0u);

    EXPECT_GT(
        stats_collector[0].finished_txns_[0].start_time_,
        stats_collector[0].start_time_);
    EXPECT_GT(
        stats_collector[0].finished_time_,
        stats_collector[0].finished_txns_[2].finished_time_);

    // In this instance, we expect txn with id = 1 to finish last *FOR SURE*
    EXPECT_EQ(stats_collector[0].finished_txns_[2].id_, 1u);
    EXPECT_EQ(stats_collector[0].finished_txns_[2].tries_.size(), 2u);
    EXPECT_EQ(
        stats_collector[0].finished_txns_[2].tries_[0].stopped_time_,
        stats_collector[0].finished_txns_[2].tries_[1].start_time_);
    EXPECT_GT(
        stats_collector[0].finished_txns_[2].tries_[0].stopped_time_,
        stats_collector[0].finished_txns_[2].tries_[0].start_time_);
    EXPECT_GT(
        stats_collector[0].finished_txns_[2].tries_[1].stopped_time_,
        stats_collector[0].finished_txns_[2].tries_[1].start_time_);
}
