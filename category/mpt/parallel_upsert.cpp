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

#include <category/mpt/parallel_upsert.hpp>

#include <category/core/assert.h>
#include <category/mpt/config.hpp>
#include <category/mpt/trie.hpp>

#include <atomic>
#include <cstdint>
#include <mutex>
#include <utility>

MONAD_MPT_NAMESPACE_BEGIN

ParallelUpsertContext::ParallelUpsertContext(
    unsigned const workers, uint32_t const partition_min_updates)
    : partition_min_updates_(partition_min_updates)
{
    MONAD_ASSERT(workers > 0);
    MONAD_ASSERT(partition_min_updates > 1);
    workers_.reserve(workers);
    for (unsigned n = 0; n < workers; ++n) {
        workers_.emplace_back([this] { run(); });
    }
}

ParallelUpsertContext::~ParallelUpsertContext()
{
    {
        std::unique_lock const g(lock_);
        MONAD_ASSERT(queue_.empty());
        stop_ = true;
    }
    cv_.notify_all();
    for (auto &worker : workers_) {
        worker.join();
    }
}

void ParallelUpsertContext::submit(Batch &batch, Partition &&partition)
{
    MONAD_ASSERT(partition.out != nullptr);
    MONAD_ASSERT(partition.sm != nullptr);
    // Growing would move the partitions the workers were handed
    MONAD_ASSERT(batch.partitions_.size() < batch.partitions_.capacity());
    batch.partitions_.push_back(std::move(partition));
    batch.remaining_.fetch_add(1, std::memory_order_relaxed);
    {
        std::unique_lock const g(lock_);
        queue_.emplace_back(&batch, &batch.partitions_.back());
    }
    // notify_all, not notify_one: a thread parked inside wait() must get the
    // chance to help, and it is parked on this same condvar.
    cv_.notify_all();
}

bool ParallelUpsertContext::try_run_one()
{
    Batch *batch = nullptr;
    Partition *partition = nullptr;
    {
        std::unique_lock const g(lock_);
        if (queue_.empty()) {
            return false;
        }
        auto const [queued_batch, queued_partition] = queue_.back();
        queue_.pop_back();
        batch = queued_batch;
        partition = queued_partition;
    }
    build_partition_subtrie(*this, *partition);
    {
        std::unique_lock const g(lock_);
        if (batch->remaining_.fetch_sub(1, std::memory_order_acq_rel) == 1) {
            cv_.notify_all();
        }
    }
    return true;
}

void ParallelUpsertContext::wait(Batch &batch)
{
    while (batch.remaining_.load(std::memory_order_acquire) != 0) {
        if (try_run_one()) {
            continue;
        }
        std::unique_lock g(lock_);
        cv_.wait(g, [this, &batch] {
            return batch.remaining_.load(std::memory_order_acquire) == 0 ||
                   !queue_.empty();
        });
    }
}

void ParallelUpsertContext::run()
{
    for (;;) {
        {
            std::unique_lock g(lock_);
            cv_.wait(g, [this] { return stop_ || !queue_.empty(); });
            if (queue_.empty()) {
                return;
            }
        }
        (void)try_run_one();
    }
}

MONAD_MPT_NAMESPACE_END
