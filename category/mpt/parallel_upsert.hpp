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
class UpdateAux;
class WorkerNodeWriter;
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
worth a handoff. A worker runs the ordinary create recursion against an
`UpdateAux` of its own that borrows the submitter's i/o and metadata, so it
builds, serializes, places and frees its own nodes: writes dispatch to the
calling thread's `WorkerNodeWriter`, which owns a byte range reserved for it
alone. Only the partition root crosses a thread boundary, as any child offset
always did.

The partitions of one trie node are submitted and awaited as a batch by the
recursion frame that cut them. A partition splits again wherever its own
sublists are still large, so in-flight parallelism is not capped at one node's
child count and a lopsided subtrie is broken up rather than serialising its
batch; to keep that deadlock free, a thread waiting on a batch runs queued
partitions itself rather than blocking while work is available. A partition that
runs on the service thread that way writes through the triedb write path as
usual, because writer selection is by thread rather than by partition.
*/
class ParallelUpsertContext
{
public:
    /*! \brief One subtrie handed to a worker.

    `out` and the `Update` objects reachable from `updates` belong to the
    submitting frame and must outlive the batch. `sm` is the worker's own clone,
    positioned at `out`'s branch.
    */
    struct Partition
    {
        ChildData *out{nullptr};
        UpdateList updates{};
        std::unique_ptr<StateMachine> sm{};
        unsigned prefix_index{0};
        timeline_id tid{timeline_id::primary};
        /* The aux the partition was cut from. The worker constructs its own
        from it, borrowing the i/o, the metadata and the timeline state, and
        never writes through its node writers. It does read the submitter's
        mutable `can_write_to_fast_` on every node write, to pick the
        destination list; that is safe only because the flag is set before the
        upsert starts and not touched again while partitions are in flight, and
        is published through the queue mutex. */
        UpdateAux *submitter{nullptr};
        // Written by the worker: the largest version in the built subtrie.
        int64_t version{0};
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
    on can always be picked up by somebody.

    A partition run this way writes through whatever writer its thread would use
    outside one, so on the triedb's own thread it goes through the node writers
    and can poll AsyncIO, which can complete a read and resume an unrelated
    frame of the update recursion. That is the same reentrancy an ordinary node
    write carries.
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

    /*! \brief Points the extent allocator at the chunk to reserve from, which
    must be the last chunk of `in_fast_list`'s list and the one the service
    thread's own writer reserves from too.

    Call exactly once, before any `reserve_extent`: re-pointing it would leave
    every live writer's extent in a chunk, or a pool, it no longer tracks.
    */
    void init_extents(
        MONAD_ASYNC_NAMESPACE::storage_pool &, uint32_t chunk_id,
        bool in_fast_list, ChunkGrant);

    //! \brief Whether `init_extents` has run, i.e. whether extents can be
    //! reserved yet.
    bool extents_ready() const noexcept
    {
        return extent_pool_ != nullptr;
    }

    /*! \brief Whether any worker can currently be inside `reserve_extent`.

    The precise guard for an unlocked `db_metadata` free-list pop: safe only
    when no worker can be mutating the same lists under `extent_lock_`.
    */
    bool no_partitions_in_flight() const noexcept
    {
        return partitions_in_flight_.load(std::memory_order_acquire) == 0;
    }

    //! \brief Whether the writer of `in_fast_list`'s list shares its chunk with
    //! this context's workers, and so must place its buffers in reserved
    //! extents rather than at the chunk's append point.
    bool owns_extents_of(bool const in_fast_list) const noexcept
    {
        return extents_ready() && extents_in_fast_list_ == in_fast_list;
    }

    //! \brief How many bytes a reservation asks for. Page multiple, never above
    //! `AsyncIO::WRITE_BUFFER_SIZE`, so one extent always fits in one write
    //! buffer.
    size_t extent_bytes() const noexcept
    {
        MONAD_ASSERT(extents_ready());
        return extent_bytes_;
    }

    /*! \brief The offset every extent handed out so far lies below, which is
    what the db's work-in-progress offset must record: a worker's extent can sit
    ahead of the service thread's own writer, and everything after the recorded
    chunk is destroyed at the next open.

    Grants a fresh chunk when the current one is exactly full, because a
    chunk-relative offset of the capacity is one past what `chunk_offset_t` can
    represent.
    */
    chunk_offset_t extent_cursor();

    /*! \brief The writer this thread serializes into, or null on any thread
    that is not one of this context's pool threads.

    Null on the triedb service thread, including while it helps inside `wait()`:
    it keeps using its own node writers and the uring path.
    */
    WorkerNodeWriter *writer_for_this_thread();

    //! \brief Writes out every pool thread's buffered nodes. The publication
    //! barrier: a root must never be published over an unflushed node.
    void flush_writers();

    //! \brief Nodes appended to a pool thread's own writer.
    size_t appended_nodes() const noexcept;

    //! \brief Partitions built by a pool thread rather than by a helping
    //! service thread.
    size_t partitions_built_by_workers() const noexcept
    {
        return partitions_built_by_workers_.load(std::memory_order_acquire);
    }

    /*! \brief Overrides the reservation size. WARNING: for unit testing only.

    A production sized extent leaves every boundary path unexecuted at test
    scale. Call before `init_extents`.
    */
    void set_extent_bytes_unit_testing_only(size_t const bytes)
    {
        MONAD_ASSERT(!extents_ready());
        extent_bytes_override_ = bytes;
    }

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
    void run(unsigned index);
    bool try_run_one();
    uint32_t grant_chunk_under_lock_();

    std::mutex lock_;
    // One condvar for both "work arrived" and "batch finished": a thread inside
    // wait() must wake for either, or nested partitions could sit in the queue
    // with every thread parked.
    std::condition_variable cv_;
    std::vector<std::pair<Batch *, Partition *>> queue_;
    std::vector<std::thread> workers_;
    uint32_t const partition_min_updates_;
    bool stop_{false};
    // Partitions submitted but not yet built, over every batch. Only read to
    // check that nothing is in flight.
    std::atomic<unsigned> partitions_in_flight_{0};
    std::atomic<size_t> partitions_built_by_workers_{0};

    /* One writer per pool thread, indexed by the thread's own index and touched
    by no other thread while a partition is in flight. Built lazily, because
    the chunk to reserve from is not known until the first upsert. */
    std::vector<std::unique_ptr<WorkerNodeWriter>> writers_;

    // Serializes the read-then-reserve pair across every writer sharing a chunk
    std::mutex extent_lock_;
    MONAD_ASYNC_NAMESPACE::storage_pool *extent_pool_{nullptr};
    ChunkGrant grant_chunk_{};
    uint32_t extent_chunk_id_{0};
    size_t extent_bytes_{0};
    size_t extent_bytes_override_{0};
    bool extents_in_fast_list_{false};
    // Set for as long as a thread is inside the grant, which must be one at a
    // time: it mutates the db_metadata chunk lists.
    std::atomic<bool> granting_{false};
};

/*! \brief Writes the nodes one worker builds into a byte range reserved for
that worker alone.

Serialization, disk offset assignment and the write itself all happen on the
building thread, through a blocking `pwrite` of the writer's own buffer. Nothing
here goes through `AsyncIO`: its ring, its shared write buffers and the
`db_metadata` mutations it makes are none of them thread safe.

Not thread safe, and deliberately so: there is exactly one instance per worker
thread, and no instance is touched by another thread while its own has work.
`ParallelUpsertContext::flush_writers` is the one exception, and it runs on the
service thread with no partition in flight. Several instances may write into the
same chunk at once — their extents are disjoint because reservation order alone
decides placement, and every reservation goes through one `ExtentSource`.
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

    size_t appended_nodes() const noexcept
    {
        return appended_nodes_;
    }

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
    size_t appended_nodes_{0};
};

/*! \brief Build a partition's subtrie, writing its nodes as they are built.

Defined in trie.cpp, which owns the create recursion. Runs on whichever thread
picked the partition up.
*/
void build_partition_subtrie(
    ParallelUpsertContext &, ParallelUpsertContext::Partition &);

MONAD_MPT_NAMESPACE_END
