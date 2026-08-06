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

#pragma once

#include <category/core/assert.h>
#include <category/mpt/config.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/update.hpp>

#include <atomic>
#include <condition_variable>
#include <cstdint>
#include <memory>
#include <mutex>
#include <thread>
#include <utility>
#include <vector>

MONAD_MPT_NAMESPACE_BEGIN

class Node;
struct ChildData;

/*! \brief Worker pool that merklizes disjoint new subtries off the triedb
service thread.

A partition is a subtrie absent from the previous version and big enough to be
worth a handoff, so a worker only builds nodes: it runs the ordinary create
recursion against a private in-memory `UpdateAux`, which suppresses every write
and leaves the whole subtrie resident, and records the post-order list of nodes
to write. The service thread walks that list to assign disk offsets, so node
serialization, offset allocation and db_metadata mutation remain single
threaded.

The partitions of one trie node are submitted and awaited as a batch by the
recursion frame that cut them. A partition splits again wherever its own
sublists are still large, so in-flight parallelism is not capped at one node's
child count and a lopsided subtrie is broken up rather than serialising its
batch; to keep that deadlock free, a thread waiting on a batch runs queued
partitions itself rather than blocking while work is available.
*/
class ParallelUpsertContext
{
public:
    /*! \brief One subtrie handed to a worker.

    `out` and the `Update` objects reachable from `updates` belong to the
    submitting frame and must outlive the batch. `sm` arrives positioned at
    `out`'s branch and is left there, so the service thread can reuse it to
    walk the finished subtrie.
    */
    /*! \brief One descendant of a finished partition, ready to be written.

    Recorded in post-order, so a parent's child offsets are final before the
    parent is serialized. `evict` is the caching decision the serial write loop
    would have made, computed on the worker where the StateMachine walk is
    parallel.
    */
    struct PendingWrite
    {
        Node *node{nullptr};
        Node *parent{nullptr};
        uint8_t index{0};
        bool evict{false};
    };

    struct Partition
    {
        ChildData *out{nullptr};
        UpdateList updates{};
        std::unique_ptr<StateMachine> sm{};
        unsigned prefix_index{0};
        timeline_id tid{timeline_id::primary};
        // Only a partition cut by the service thread needs a write list; a
        // nested one is covered by its parent partition's walk.
        bool collect_writes{false};
        // Written by the worker: the largest version in the built subtrie.
        int64_t version{0};
        std::vector<PendingWrite> writes{};
    };

    /*! \brief The partitions of one trie node, awaited together.

    A batch interrupted by a reentrant recursion (a write can complete a read,
    which resumes an unrelated frame) is independent of any batch nested inside
    it: each frame waits only on its own partitions.
    */
    class Batch
    {
        friend class ParallelUpsertContext;

        std::vector<Partition> partitions_;
        std::atomic<unsigned> remaining_{0};

    public:
        // Partition addresses are handed to workers, so the storage is sized
        // once here and never grown.
        explicit Batch(size_t const capacity)
        {
            partitions_.reserve(capacity);
        }

        Batch(Batch const &) = delete;
        Batch &operator=(Batch const &) = delete;

        ~Batch()
        {
            MONAD_ASSERT(remaining_.load(std::memory_order_acquire) == 0);
        }

        // Complete only once wait() has returned.
        std::vector<Partition> &partitions() noexcept
        {
            return partitions_;
        }
    };

    ParallelUpsertContext(unsigned workers, uint32_t partition_min_updates);
    ~ParallelUpsertContext();

    ParallelUpsertContext(ParallelUpsertContext const &) = delete;
    ParallelUpsertContext &operator=(ParallelUpsertContext const &) = delete;

    uint32_t partition_min_updates() const noexcept
    {
        return partition_min_updates_;
    }

    void submit(Batch &, Partition &&);

    /*! \brief Runs queued partitions until every partition of `batch` is built.

    Helps rather than idles, which is what makes nested partitions safe: a
    thread only blocks when the queue is empty, so the work its batch is waiting
    on can always be picked up by somebody. Never polls the caller's AsyncIO, so
    waiting cannot reenter the caller's own update recursion through an i/o
    completion.
    */
    void wait(Batch &);

private:
    void run();
    bool try_run_one();

    std::mutex lock_;
    // One condvar for both "work arrived" and "batch finished": a thread inside
    // wait() must wake for either, or nested partitions could sit in the queue
    // with every thread parked.
    std::condition_variable cv_;
    std::vector<std::pair<Batch *, Partition *>> queue_;
    std::vector<std::thread> workers_;
    uint32_t const partition_min_updates_;
    bool stop_{false};
};

/*! \brief Build a partition's subtrie in memory and record its write list.

Defined in trie.cpp, which owns the create recursion. Runs on whichever thread
picked the partition up.
*/
void build_partition_subtrie(
    ParallelUpsertContext &, ParallelUpsertContext::Partition &);

MONAD_MPT_NAMESPACE_END
