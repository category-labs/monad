#include <monad/execution/stats/stats.hpp>
#include <monad/execution/stats/stats_writer.hpp>

MONAD_EXECUTION_STATS_NAMESPACE_BEGIN

std::mutex StatsWriter::mutex_;

void StatsWriter::start_block(BlockStats &bs)
{
    bs.start_time_ = std::chrono::steady_clock::now();
}

void StatsWriter::finish_block(BlockStats &bs)
{
    bs.finished_time_ = std::chrono::steady_clock::now();
    bs.elapsed_ms_ = static_cast<uint64_t>(
        std::chrono::duration_cast<std::chrono::milliseconds>(
            bs.finished_time_ - bs.start_time_)
            .count());
}

// TODO: should I mark this function as noexcept?
void StatsWriter::start_txn(BlockStats &bs, size_t id)
{
    std::lock_guard<std::mutex> lock(mutex_);
    if (bs.running_txns_map_.find(id) == bs.running_txns_map_.end()) {
        TxnStats txn_stats(bs.block_.transactions[id], id);
        txn_stats.start_time_ = std::chrono::steady_clock::now();
        TxnStats::Tries t{.start_time_ = txn_stats.start_time_};
        txn_stats.tries_.emplace_back(t);

        bs.running_txns_.emplace_back(txn_stats);
        bs.running_txns_map_.emplace(id, bs.running_txns_.size() - 1u);
    }
    else {
        size_t pos_in_vector = bs.running_txns_map_[id];
        MONAD_ASSERT(!bs.running_txns_[id].tries_.empty());
        auto &last_try = bs.running_txns_[pos_in_vector].tries_.back();
        last_try.stopped_time_ = std::chrono::steady_clock::now();
        last_try.elapsed_ms_ = static_cast<uint64_t>(
            std::chrono::duration_cast<std::chrono::milliseconds>(
                last_try.stopped_time_ - last_try.start_time_)
                .count());

        TxnStats::Tries t{.start_time_ = last_try.stopped_time_};
        bs.running_txns_[id].tries_.emplace_back(t);
    }
}

void StatsWriter::finish_txn(BlockStats &bs, size_t id)
{
    std::lock_guard<std::mutex> lock(mutex_);
    MONAD_ASSERT(bs.running_txns_map_.find(id) != bs.running_txns_map_.end());
    size_t pos_in_vector = bs.running_txns_map_[id];

    auto &last_try = bs.running_txns_[pos_in_vector].tries_.back();
    last_try.stopped_time_ = std::chrono::steady_clock::now();
    last_try.elapsed_ms_ = static_cast<uint64_t>(
        std::chrono::duration_cast<std::chrono::milliseconds>(
            last_try.stopped_time_ - last_try.start_time_)
            .count());

    bs.running_txns_[pos_in_vector].finished_time_ =
        std::chrono::steady_clock::now();
    bs.running_txns_[pos_in_vector].elapsed_ms_ = static_cast<uint64_t>(
        std::chrono::duration_cast<std::chrono::milliseconds>(
            bs.running_txns_[pos_in_vector].finished_time_ -
            bs.running_txns_[pos_in_vector].start_time_)
            .count());

    bs.finished_txns_.emplace_back(bs.running_txns_[pos_in_vector]);
    bs.running_txns_.erase(
        bs.running_txns_.begin() + static_cast<int>(pos_in_vector));
}

// TODO
void StatsWriter::take_snapshot([[maybe_unused]] BlockStats &bs) {}

MONAD_EXECUTION_STATS_NAMESPACE_END