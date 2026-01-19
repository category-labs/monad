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

#include <category/async/io.hpp>
#include <category/async/uring_fiber_scheduler.hpp>
#include <category/core/assert.h>
#include <category/mpt/config.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/util.hpp>

#include <boost/fiber/context.hpp>
#include <boost/fiber/operations.hpp>

#include <cstring>

MONAD_MPT_NAMESPACE_BEGIN

// Read a node from disk using fiber-based IO.
// This replaces async_read + node_receiver_t pattern with a simpler
// synchronous-looking interface that yields the fiber during IO.
//
// @param io The AsyncIO instance
// @param offset The chunk offset to read from (includes page count in spare)
// @return The deserialized node
inline Node::SharedPtr
fiber_read_node(async::AsyncIO &io, chunk_offset_t offset)
{
    // Calculate read parameters from offset
    auto const num_pages = node_disk_pages_spare_15{offset}.to_pages();
    auto const bytes_to_read =
        static_cast<unsigned>(num_pages << DISK_PAGE_BITS);
    auto const rd_offset_value =
        round_down_align<DISK_PAGE_BITS>(offset.offset);
    auto const buffer_offset =
        static_cast<uint16_t>(offset.offset - rd_offset_value);

    // Create page-aligned read offset
    chunk_offset_t rd_offset = offset;
    rd_offset.offset = rd_offset_value & chunk_offset_t::max_offset;
    rd_offset.set_spare(0);

    // Create completion token on stack
    monad::fiber::CompletionToken token;
    token.waiting_fiber = boost::fibers::context::active();

    // Handle short vs long reads
    if (bytes_to_read <= async::AsyncIO::READ_BUFFER_SIZE) {
        // Short read - use pool buffer
        auto buffer = io.fiber_get_read_buffer();

        // Submit read
        io.submit_fiber_read(
            std::span<std::byte>(buffer.get(), bytes_to_read),
            rd_offset,
            &token);

        // Suspend until completion - scheduler polls io_uring and wakes us
        auto *ctx = boost::fibers::context::active();
        while (!token.completed) {
            ctx->suspend();
        }

        MONAD_ASSERT(token.result >= 0);
        MONAD_ASSERT(token.result == static_cast<int32_t>(bytes_to_read));

        // Deserialize node from buffer
        return deserialize_node_from_buffer(
            reinterpret_cast<unsigned char const *>(buffer.get()) +
                buffer_offset,
            bytes_to_read - buffer_offset);
    }
    else {
        // Long read - allocate separate buffer
        std::byte *buffer = static_cast<std::byte *>(
            aligned_alloc(DISK_PAGE_SIZE, bytes_to_read));
        MONAD_ASSERT(buffer != nullptr);

        // Submit read
        io.submit_fiber_read(
            std::span<std::byte>(buffer, bytes_to_read), rd_offset, &token);

        // Suspend until completion - scheduler polls io_uring and wakes us
        auto *ctx = boost::fibers::context::active();
        while (!token.completed) {
            ctx->suspend();
        }

        MONAD_ASSERT(token.result >= 0);
        MONAD_ASSERT(token.result == static_cast<int32_t>(bytes_to_read));

        // Deserialize node from buffer
        auto node = deserialize_node_from_buffer(
            reinterpret_cast<unsigned char const *>(buffer) + buffer_offset,
            bytes_to_read - buffer_offset);

        // Free the allocated buffer
        free(buffer);

        return node;
    }
}

// Fiber-based write buffer for accumulating node data and flushing to disk.
// Uses fiber-friendly IO that yields during write operations.
//
// Usage:
//   FiberWriteBuffer buf(io, start_offset);
//   while (has_data) {
//       auto* ptr = buf.reserve(size);  // May yield if buffer full
//       serialize_to(ptr);
//       buf.commit(size);
//   }
//   buf.flush();  // Yields until final write completes
//
class FiberWriteBuffer
{
    async::AsyncIO *io_;
    async::AsyncIO::write_buffer_ptr buffer_;
    chunk_offset_t start_offset_;
    size_t written_{0};
    size_t capacity_;

public:
    FiberWriteBuffer(async::AsyncIO &io, chunk_offset_t start_offset)
        : io_(&io)
        , buffer_(io.fiber_get_write_buffer())
        , start_offset_(start_offset)
        , capacity_(async::AsyncIO::WRITE_BUFFER_SIZE)
    {
        MONAD_ASSERT(buffer_ != nullptr);
    }

    // Non-copyable, movable
    FiberWriteBuffer(FiberWriteBuffer const &) = delete;
    FiberWriteBuffer &operator=(FiberWriteBuffer const &) = delete;
    FiberWriteBuffer(FiberWriteBuffer &&) = default;
    FiberWriteBuffer &operator=(FiberWriteBuffer &&) = default;

    ~FiberWriteBuffer()
    {
        // Buffer is automatically returned to pool via unique_ptr destructor
    }

    [[nodiscard]] size_t remaining() const noexcept
    {
        return capacity_ - written_;
    }

    [[nodiscard]] size_t written_bytes() const noexcept
    {
        return written_;
    }

    [[nodiscard]] chunk_offset_t start_offset() const noexcept
    {
        return start_offset_;
    }

    [[nodiscard]] chunk_offset_t current_offset() const noexcept
    {
        return start_offset_.add_to_offset(written_);
    }

    // Get pointer to write data. Caller must call commit() after writing.
    // Returns nullptr if size > remaining.
    [[nodiscard]] std::byte *reserve(size_t size) noexcept
    {
        if (size > remaining()) {
            return nullptr;
        }
        return buffer_.get() + written_;
    }

    // Commit bytes that were written via reserve()
    void commit(size_t size) noexcept
    {
        MONAD_DEBUG_ASSERT(size <= remaining());
        written_ += size;
    }

    // Append data directly to buffer. Returns nullptr if size > remaining.
    std::byte *append(size_t size) noexcept
    {
        auto *ptr = reserve(size);
        if (ptr) {
            commit(size);
        }
        return ptr - size; // Return start of appended region
    }

    // Flush current buffer contents to disk. Yields fiber until IO completes.
    // After flush, the buffer is empty and ready for reuse.
    // Returns the offset that was written to.
    chunk_offset_t flush()
    {
        if (written_ == 0) {
            return start_offset_;
        }

        // Pad to disk page alignment (DISK_PAGE_SIZE = 512 bytes)
        size_t padded_size = round_up_align<DISK_PAGE_BITS>(written_);
        if (padded_size > written_) {
            std::memset(buffer_.get() + written_, 0, padded_size - written_);
        }

        // Create completion token on stack - valid while fiber is suspended
        monad::fiber::CompletionToken token;
        token.waiting_fiber = boost::fibers::context::active();

        // Submit write via AsyncIO which handles chunk-to-file-offset
        // conversion
        io_->submit_fiber_write(
            std::span<std::byte const>(buffer_.get(), padded_size),
            start_offset_,
            &token);

        // Suspend the fiber until the completion handler wakes us.
        // Unlike yield(), suspend() does NOT re-add us to the ready queue.
        // The scheduler's poll will schedule() us when IO completes.
        auto *ctx = boost::fibers::context::active();
        while (!token.completed) {
            ctx->suspend();
        }

        MONAD_ASSERT(token.result >= 0);
        MONAD_ASSERT(token.result == static_cast<int32_t>(padded_size));

        auto flushed_offset = start_offset_;

        // Update offset for next writes
        start_offset_ = start_offset_.add_to_offset(padded_size);
        written_ = 0;

        return flushed_offset;
    }

    // Flush and get a new buffer for continued writing at a new offset.
    // Use this when crossing chunk boundaries.
    // This handles the case where normal flush would exceed max_offset.
    void flush_and_reset(chunk_offset_t new_offset)
    {
        if (written_ == 0) {
            start_offset_ = new_offset;
            return;
        }

        // Pad to disk page alignment (DISK_PAGE_SIZE = 512 bytes)
        size_t padded_size = round_up_align<DISK_PAGE_BITS>(written_);
        if (padded_size > written_) {
            std::memset(buffer_.get() + written_, 0, padded_size - written_);
        }

        // Create completion token on stack
        monad::fiber::CompletionToken token;
        token.waiting_fiber = boost::fibers::context::active();

        // Submit write to current chunk
        io_->submit_fiber_write(
            std::span<std::byte const>(buffer_.get(), padded_size),
            start_offset_,
            &token);

        // Suspend until completion - scheduler polls io_uring and wakes us
        auto *ctx = boost::fibers::context::active();
        while (!token.completed) {
            ctx->suspend();
        }

        MONAD_ASSERT(token.result >= 0);
        MONAD_ASSERT(token.result == static_cast<int32_t>(padded_size));

        // Reset to new chunk - don't update old start_offset_ since we're
        // switching chunks anyway
        start_offset_ = new_offset;
        written_ = 0;
    }
};

MONAD_MPT_NAMESPACE_END
