#pragma once

#include <monad/execution/stats/stats.hpp>
#include <mutex>

MONAD_EXECUTION_STATS_NAMESPACE_BEGIN

// All methods should be static
struct StatsWriter
{
    static std::mutex mutex_;
    static void start_block(BlockStats &bs);
    static void finish_block(BlockStats &bs);

    // should handle both first start & restart
    static void start_txn(BlockStats &bs, size_t txn_id);
    static void finish_txn(BlockStats &bs, size_t txn_id);

    static void take_snapshot(
        BlockStats &bs, std::chrono::_V2::steady_clock::time_point time);
};

MONAD_EXECUTION_STATS_NAMESPACE_END