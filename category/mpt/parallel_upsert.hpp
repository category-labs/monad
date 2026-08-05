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

#include <category/async/config.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/assert.h>
#include <category/mpt/config.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/util.hpp>

#include <atomic>
#include <condition_variable>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <mutex>
#include <thread>
#include <utility>
#include <vector>

MONAD_MPT_NAMESPACE_BEGIN

class Node;
struct ChildData;

//! \brief A byte range reserved for one writer inside one sequential chunk.
struct ExtentReservation
{
    uint32_t chunk_id;
    file_offset_t base; // chunk relative, DISK_PAGE_SIZE aligned
    size_t bytes; // multiple of DISK_PAGE_SIZE
};

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

    /*! \brief Returns the id of a sequential chunk to take extents from.

    The chunk must already be appended to the fast list: reserving space in a
    chunk is not the same as listing it, and `physical_to_virtual` yields
    `INVALID_VIRTUAL_OFFSET` for a chunk still on the free list, which would
    make every subtrie minimum computed from an offset in it silently too high.

    Runs under `extent_lock_`, so it must not block on another thread.
    */
    using ChunkGrant = std::function<uint32_t()>;

    //! \brief Points the extent allocator at the chunk to reserve from. Call
    //! exactly once, before any `reserve_extent`: re-pointing it would leave
    //! every live writer's extent in a chunk, or a pool, it no longer tracks.
    void init_extents(
        MONAD_ASYNC_NAMESPACE::storage_pool &, uint32_t chunk_id, ChunkGrant);

    /*! \brief Reserves the next extent, of between `min_bytes` and
    `want_bytes`, granting a new chunk when the current one cannot hold
    `min_bytes`.

    Callable from any thread, with or without a `WorkerNodeWriter`: the service
    thread's own writer reserves through here too once a parallel upsert is in
    flight, which is what keeps the extents of every writer disjoint.

    The remainder read and the reservation that consumes it are one critical
    section. Two reservers that both read the same remainder would both clamp to
    it and both reserve it, and the loser would trip `chunk_t::reserve`'s
    capacity assert.

    Lock ordering: `extent_lock_` then `storage_pool::lock_`, which
    `storage_pool::chunk()` takes twice per call from inside here. Acyclic
    because nothing in `async` can call back into `mpt`. `extent_lock_` is not
    taken with the partition queue's `lock_` held either way, and no thread may
    hold it across a partition build, which would deadlock against the batch
    that build waits on. The chunk grant runs inside it, so the grant must not
    block.
    */
    ExtentReservation reserve_extent(size_t min_bytes, size_t want_bytes);

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

    // Serializes the read-then-reserve pair across every writer sharing a chunk
    std::mutex extent_lock_;
    MONAD_ASYNC_NAMESPACE::storage_pool *extent_pool_{nullptr};
    ChunkGrant grant_chunk_{};
    uint32_t extent_chunk_id_{0};
};

/*! \brief Writes the nodes one worker builds into a byte range reserved for
that worker alone.

Serialization, disk offset assignment and the write itself all happen on the
building thread, through a blocking `pwrite` of the writer's own buffer. Nothing
here goes through `AsyncIO`: its ring, its shared write buffers and the
`db_metadata` mutations it makes are none of them thread safe.

Not thread safe, and deliberately so: there is exactly one instance per worker
thread, and no instance is ever touched by a thread other than its own. Several
instances may write into the same chunk at once — their extents are disjoint
because reservation order alone decides placement, and every reservation goes
through one `ExtentSource`.
*/
class WorkerNodeWriter
{
public:
    //! \brief Reserves an extent of between `min_bytes` and `want_bytes`.
    //! `ParallelUpsertContext::reserve_extent` in production, which is what
    //! makes concurrent reservations of one chunk safe.
    using ExtentSource =
        std::function<ExtentReservation(size_t min_bytes, size_t want_bytes)>;

    WorkerNodeWriter(
        MONAD_ASYNC_NAMESPACE::storage_pool &, size_t extent_bytes,
        ExtentSource);

    ~WorkerNodeWriter();

    WorkerNodeWriter(WorkerNodeWriter const &) = delete;
    WorkerNodeWriter &operator=(WorkerNodeWriter const &) = delete;

    //! \brief Serializes `node` and returns the physical offset it will live
    //! at, with the spare page count set as `async_write_node_set_spare` does.
    chunk_offset_t append(Node const &);

    /*! \brief Writes whatever is buffered, padded to `DISK_PAGE_SIZE`.

    The extent is retained: the next `append` continues inside it at the page
    boundary this flush ended on, so no byte is ever written twice and the
    unwritten tail of the reservation is not orphaned.
    */
    void flush();

private:
    ExtentReservation reserve_(size_t min_bytes, size_t want_bytes);
    chunk_offset_t append_oversized_(Node const &, uint32_t disk_size);
    void write_(
        uint32_t chunk_id, file_offset_t base, unsigned char const *,
        size_t bytes);

    MONAD_ASYNC_NAMESPACE::storage_pool &pool_;
    ExtentSource extent_source_;
    // DISK_PAGE_SIZE aligned and extent_bytes_ long, because the pool's write
    // fd can be O_DIRECT: buffer address, length and file offset all have to be
    // page aligned
    unsigned char *buf_{nullptr};
    size_t const extent_bytes_; // reservation size to ask for, page multiple
    uint32_t extent_chunk_id_{0}; // chunk holding the current extent
    // base_ is where the extent starts within extent_chunk_id_; len_, used_ and
    // flushed_ are relative to base_, and buf_ mirrors the extent from its
    // start. base_ + used_ is where the next node goes, base_ + flushed_ the
    // first byte not yet on disk. Invariant: flushed_ <= used_ <= len_, with
    // flushed_ a multiple of DISK_PAGE_SIZE and len_ == 0 until the first
    // extent is reserved.
    file_offset_t base_{0};
    size_t len_{0};
    size_t used_{0};
    size_t flushed_{0};
};

/*! \brief Build a partition's subtrie in memory and record its write list.

Defined in trie.cpp, which owns the create recursion. Runs on whichever thread
picked the partition up.
*/
void build_partition_subtrie(
    ParallelUpsertContext &, ParallelUpsertContext::Partition &);

MONAD_MPT_NAMESPACE_END
