#pragma once

#include <monad/core/block.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/config.hpp>

#include <monad/execution/stats/stats.hpp>
#include <monad/execution/stats/stats_writer.hpp>

#include <vector>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <class TExecution>
struct AllTxnBlockProcessor
{
    template <
        class TState, class TFiberData, class TStatsCollector,
        class TStatsWriter>
    [[nodiscard]] std::vector<Receipt>
    execute(TState &s, Block const &b, TStatsCollector &stats_collector)
    {
        std::vector<TFiberData> data{};
        std::vector<typename TExecution::fiber_t> fibers{};

        data.reserve(b.transactions.size());
        fibers.reserve(b.transactions.size());

        stats::BlockStats block_stats(b);
        TStatsWriter::start_block(block_stats);

        int i = 0;
        for (auto const &txn : b.transactions) {
            data.push_back({s, txn, b.header, i, block_stats});
            fibers.emplace_back(data.back());
            ++i;
        }
        TExecution::yield();

        std::vector<Receipt> r{};
        r.reserve(b.transactions.size());
        for (auto &fiber : fibers) {
            fiber.join();
        }

        TStatsWriter::finish_block(block_stats);
        stats_collector.emplace_back(block_stats);

        for (auto &d : data) {
            r.push_back(d.get_receipt());
        }
        return r;
    }
};

MONAD_EXECUTION_NAMESPACE_END
