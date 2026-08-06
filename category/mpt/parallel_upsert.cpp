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

#include <category/async/config.hpp>
#include <category/async/io.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/util.hpp>

#include <algorithm>
#include <atomic>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <mutex>
#include <utility>

#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

/* Which pool thread of which context this is. Unset on the triedb service
thread, including while it helps inside wait(), so writer selection is by thread
rather than by partition. */
thread_local MONAD_MPT_NAMESPACE::ParallelUpsertContext const
    *tls_pool_context = nullptr;
thread_local unsigned tls_pool_index = 0;

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_MPT_NAMESPACE_BEGIN

WorkerNodeWriter::WorkerNodeWriter(
    MONAD_ASYNC_NAMESPACE::storage_pool &pool, size_t const extent_bytes,
    ExtentSource extent_source)
    : pool_(pool)
    , extent_source_(std::move(extent_source))
    , extent_bytes_(extent_bytes)
{
    MONAD_ASSERT(extent_source_ != nullptr);
    MONAD_ASSERT(extent_bytes > 0);
    MONAD_ASSERT(extent_bytes == round_up_align<DISK_PAGE_BITS>(extent_bytes));
    buf_ = static_cast<unsigned char *>(
        ::aligned_alloc(DISK_PAGE_SIZE, extent_bytes));
    MONAD_ASSERT(buf_ != nullptr);
}

WorkerNodeWriter::~WorkerNodeWriter()
{
    // Discarding buffered nodes would leave their parents pointing at offsets
    // nothing was ever written to
    MONAD_ASSERT(used_ == flushed_);
    ::free(buf_);
}

ExtentReservation
WorkerNodeWriter::reserve_(size_t const min_bytes, size_t const want_bytes)
{
    auto const at = extent_source_(min_bytes, want_bytes);
    // The source is injected, so validate what the write path relies on: an
    // extent longer than was asked for would not fit buf_, and one that is not
    // page aligned would break every O_DIRECT write into it
    MONAD_ASSERT(at.bytes >= min_bytes);
    MONAD_ASSERT(at.bytes <= want_bytes);
    MONAD_ASSERT(at.base == round_down_align<DISK_PAGE_BITS>(at.base));
    MONAD_ASSERT(at.bytes == round_down_align<DISK_PAGE_BITS>(at.bytes));
    return at;
}

void WorkerNodeWriter::write_(
    uint32_t const chunk_id, file_offset_t const base,
    unsigned char const *const buffer, size_t const bytes)
{
    auto const [fd, offset] =
        pool_.chunk(MONAD_ASYNC_NAMESPACE::storage_pool::seq, chunk_id)
            .write_offset(base);
    ssize_t const bytes_written =
        ::pwrite(fd, buffer, bytes, static_cast<off_t>(offset));
    MONAD_ASSERT_PRINTF(
        bytes_written == static_cast<ssize_t>(bytes),
        "pwrite of %zu bytes at %llu returned %zd due to %s",
        bytes,
        static_cast<unsigned long long>(offset),
        bytes_written,
        bytes_written < 0 ? strerror(errno) : "a short write");
}

chunk_offset_t
WorkerNodeWriter::append_oversized_(Node const &node, uint32_t const disk_size)
{
    size_t const bytes =
        round_up_align<DISK_PAGE_BITS>(static_cast<size_t>(disk_size));
    auto const at = reserve_(bytes, bytes);
    auto *const buffer =
        static_cast<unsigned char *>(::aligned_alloc(DISK_PAGE_SIZE, bytes));
    MONAD_ASSERT(buffer != nullptr);
    serialize_node_to_buffer(buffer, disk_size, node, disk_size);
    memset(buffer + disk_size, 0, bytes - disk_size);
    write_(at.chunk_id, at.base, buffer, bytes);
    ::free(buffer);
    chunk_offset_t offset{at.chunk_id, at.base};
    offset.set_spare(static_cast<uint16_t>(
        node_disk_pages_spare_15{num_pages(offset.offset, disk_size)}));
    ++appended_nodes_;
    return offset;
}

chunk_offset_t WorkerNodeWriter::append(Node const &node)
{
    auto const disk_size = node.get_disk_size();
    if (disk_size > len_ - used_) {
        if (disk_size > extent_bytes_) {
            return append_oversized_(node, disk_size);
        }
        flush();
        auto const at = reserve_(
            round_up_align<DISK_PAGE_BITS>(static_cast<size_t>(disk_size)),
            extent_bytes_);
        extent_chunk_id_ = at.chunk_id;
        base_ = at.base;
        len_ = at.bytes;
        used_ = flushed_ = 0;
        MONAD_ASSERT(disk_size <= len_);
    }
    serialize_node_to_buffer(buf_ + used_, disk_size, node, disk_size);
    chunk_offset_t offset{extent_chunk_id_, base_ + used_};
    offset.set_spare(static_cast<uint16_t>(
        node_disk_pages_spare_15{num_pages(offset.offset, disk_size)}));
    used_ += disk_size;
    ++appended_nodes_;
    return offset;
}

void WorkerNodeWriter::flush()
{
    MONAD_ASSERT(flushed_ <= used_);
    if (used_ == flushed_) {
        return;
    }
    size_t const padded = round_up_align<DISK_PAGE_BITS>(used_);
    MONAD_ASSERT(padded <= len_);
    memset(buf_ + used_, 0, padded - used_);
    write_(
        extent_chunk_id_, base_ + flushed_, buf_ + flushed_, padded - flushed_);
    // The padding is given up rather than reused, which is what keeps a flush
    // from rewriting a byte the previous one already wrote
    used_ = flushed_ = padded;
}

void ParallelUpsertContext::init_extents(
    MONAD_ASYNC_NAMESPACE::storage_pool &pool, uint32_t const chunk_id,
    bool const in_fast_list, ChunkGrant grant_chunk)
{
    MONAD_ASSERT(grant_chunk != nullptr);
    std::unique_lock const g(extent_lock_);
    // Re-pointing the allocator would leave every live writer's extent in a
    // chunk, or a pool, the allocator no longer knows about
    MONAD_ASSERT(extent_pool_ == nullptr);
    extent_chunk_id_ = chunk_id;
    grant_chunk_ = std::move(grant_chunk);
    extents_in_fast_list_ = in_fast_list;
    if (extent_bytes_override_ != 0) {
        extent_bytes_ = extent_bytes_override_;
    }
    else {
        /* One write buffer, which is a thirty-second of a production chunk.
        Writers that each hold a larger fraction than that exhaust the free list
        long before they have filled what they hold, so a smaller chunk scales
        the extent down with it rather than handing one writer the lot. */
        static constexpr size_t CHUNK_FRACTION = 32;
        auto const capacity =
            pool.chunk(MONAD_ASYNC_NAMESPACE::storage_pool::seq, chunk_id)
                .capacity();
        extent_bytes_ = std::min(
            MONAD_ASYNC_NAMESPACE::AsyncIO::WRITE_BUFFER_SIZE,
            static_cast<size_t>(
                round_down_align<DISK_PAGE_BITS>(capacity / CHUNK_FRACTION)));
    }
    MONAD_ASSERT(extent_bytes_ > 0);
    MONAD_ASSERT(
        extent_bytes_ <= MONAD_ASYNC_NAMESPACE::AsyncIO::WRITE_BUFFER_SIZE);
    MONAD_ASSERT(
        extent_bytes_ == round_down_align<DISK_PAGE_BITS>(extent_bytes_));
    // Published last: extents_ready() is read without the lock by the service
    // thread deciding whether its own writer must reserve through here
    extent_pool_ = &pool;
}

uint32_t ParallelUpsertContext::grant_chunk_under_lock_()
{
    /* The grant mutates the db_metadata chunk lists, which tolerate one mutator
    at a time and cannot themselves detect a second. `extent_lock_`, which both
    callers hold, is what provides that; this flag is here to catch a caller
    added later that does not, and the grant must not block on another thread.
    */
    bool const was_granting =
        granting_.exchange(true, std::memory_order_acq_rel);
    MONAD_ASSERT(!was_granting);
    auto const chunk_id = grant_chunk_();
    granting_.store(false, std::memory_order_release);
    return chunk_id;
}

chunk_offset_t ParallelUpsertContext::extent_cursor()
{
    std::unique_lock const g(extent_lock_);
    MONAD_ASSERT(extent_pool_ != nullptr);
    auto const &chunk = [this]() -> decltype(auto) {
        return extent_pool_->chunk(
            MONAD_ASYNC_NAMESPACE::storage_pool::seq, extent_chunk_id_);
    };
    /* A chunk with nothing left cannot be resumed from: an offset of the
    capacity is one past what chunk_offset_t holds for a full sized chunk, and
    try_trim_contents cannot punch a zero length hole at it either. */
    if (chunk().reserved_bytes() >= chunk().capacity()) {
        extent_chunk_id_ = grant_chunk_under_lock_();
        MONAD_ASSERT(chunk().reserved_bytes() == 0);
    }
    return {extent_chunk_id_, chunk().reserved_bytes()};
}

ExtentReservation ParallelUpsertContext::reserve_extent(
    size_t const min_bytes, size_t const want_bytes)
{
    MONAD_ASSERT(min_bytes <= want_bytes);
    // Reading the remainder and reserving out of it must not be separable: two
    // reservers that both saw the same remainder would both clamp to it and
    // both reserve it, and the loser would trip chunk_t::reserve's capacity
    // assert
    std::unique_lock const g(extent_lock_);
    MONAD_ASSERT(extent_pool_ != nullptr);
    auto const available = [this] {
        auto const &chunk = extent_pool_->chunk(
            MONAD_ASYNC_NAMESPACE::storage_pool::seq, extent_chunk_id_);
        return static_cast<size_t>(round_down_align<DISK_PAGE_BITS>(
            chunk.capacity() - chunk.reserved_bytes()));
    };
    auto space = available();
    if (space < min_bytes) {
        extent_chunk_id_ = grant_chunk_under_lock_();
        space = available();
        MONAD_ASSERT_PRINTF(
            space >= min_bytes,
            "granted chunk %u has %zu bytes left, %zu are needed",
            extent_chunk_id_,
            space,
            min_bytes);
    }
    auto const bytes = std::min(want_bytes, space);
    auto const base =
        extent_pool_
            ->chunk(MONAD_ASYNC_NAMESPACE::storage_pool::seq, extent_chunk_id_)
            .reserve(bytes);
    // A co-reserver that reserved a non-page multiple would misalign everyone
    // downstream of it, so catch it where the reservations are made
    MONAD_ASSERT(base == round_down_align<DISK_PAGE_BITS>(base));
    return {extent_chunk_id_, base, bytes};
}

ParallelUpsertContext::ParallelUpsertContext(
    unsigned const workers, uint32_t const partition_min_updates)
    : partition_min_updates_(partition_min_updates)
{
    MONAD_ASSERT(workers > 0);
    MONAD_ASSERT(partition_min_updates > 1);
    writers_.resize(workers);
    workers_.reserve(workers);
    for (unsigned n = 0; n < workers; ++n) {
        workers_.emplace_back([this, n] { run(n); });
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
    MONAD_ASSERT(partition.submitter != nullptr);
    // Growing would move the partitions the workers were handed
    MONAD_ASSERT(batch.partitions_.size() < batch.partitions_.capacity());
    batch.partitions_.push_back(std::move(partition));
    batch.remaining_.fetch_add(1, std::memory_order_relaxed);
    // Release, so the acquire load in no_partitions_in_flight() is paired and
    // actually carries the guarantee its callers rely on
    partitions_in_flight_.fetch_add(1, std::memory_order_release);
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
    if (tls_pool_context == this) {
        partitions_built_by_workers_.fetch_add(1, std::memory_order_release);
    }
    {
        std::unique_lock const g(lock_);
        partitions_in_flight_.fetch_sub(1, std::memory_order_release);
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

void ParallelUpsertContext::run(unsigned const index)
{
    tls_pool_context = this;
    tls_pool_index = index;
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

WorkerNodeWriter *ParallelUpsertContext::writer_for_this_thread()
{
    if (tls_pool_context != this) {
        return nullptr;
    }
    auto &writer = writers_[tls_pool_index];
    if (writer == nullptr) {
        std::unique_lock const g(extent_lock_);
        MONAD_ASSERT(extent_pool_ != nullptr);
        writer = std::make_unique<WorkerNodeWriter>(
            *extent_pool_,
            extent_bytes_,
            [this](size_t const min_bytes, size_t const want_bytes) {
                return reserve_extent(min_bytes, want_bytes);
            });
    }
    return writer.get();
}

void ParallelUpsertContext::flush_writers()
{
    /* Runs on the service thread with nothing in flight, so no writer is in use
    by its owner. Each worker's appends happen before the batch completion this
    thread acquired in wait(), which is what makes its buffer visible here. */
    MONAD_ASSERT(partitions_in_flight_.load(std::memory_order_acquire) == 0);
    for (auto &writer : writers_) {
        if (writer != nullptr) {
            writer->flush();
        }
    }
}

size_t ParallelUpsertContext::appended_nodes() const noexcept
{
    size_t total = 0;
    for (auto const &writer : writers_) {
        if (writer != nullptr) {
            total += writer->appended_nodes();
        }
    }
    return total;
}

MONAD_MPT_NAMESPACE_END
