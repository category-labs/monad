#pragma once

#include <monad/execution/stats/config.hpp>

#include <monad/core/account.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/transaction.hpp>

#include <chrono>
#include <unordered_map>
#include <vector>

MONAD_EXECUTION_STATS_NAMESPACE_BEGIN

/*
Currently only doing things at txn level
State level details will be added later
*/

struct TxnStats
{
    Transaction txn_;

    TxnStats(Transaction t, size_t id) noexcept
        : txn_{t}
        , id_{id}
    {
    }

    size_t id_;
    int status_; // not used currently
    std::chrono::_V2::steady_clock::time_point start_time_;
    std::chrono::_V2::steady_clock::time_point finished_time_;
    uint64_t elapsed_ms_;

    // txn might fail due to optimistic execution
    // so we include all the tries, should include info like states touched
    // but since state is not fully ready yet, just this interface for now
    struct Tries
    {
        std::chrono::_V2::steady_clock::time_point start_time_;
        std::chrono::_V2::steady_clock::time_point stopped_time_;
        uint64_t elapsed_ms_;
    };

    std::vector<Tries> tries_;
};

struct BlockStats
{
    Block block_;

    explicit BlockStats(Block b) noexcept
        : block_{b}
    {
    }

    std::vector<TxnStats> finished_txns_;
    std::vector<TxnStats> running_txns_;
    std::unordered_map<size_t, size_t> running_txns_map_;

    std::chrono::_V2::steady_clock::time_point start_time_;
    std::chrono::_V2::steady_clock::time_point finished_time_;
    uint64_t elapsed_ms_;

    struct Snapshot
    {
        std::chrono::_V2::steady_clock::time_point time_;
        std::vector<TxnStats> finished_txns_;
        std::vector<TxnStats> running_txns_;
    };

    std::vector<Snapshot> snapshots_;
};

MONAD_EXECUTION_STATS_NAMESPACE_END