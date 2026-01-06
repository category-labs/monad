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
#include <category/core/assert.h>
#include <category/core/fiber/uring_write_scheduler.hpp>
#include <category/mpt/config.hpp>

#include <boost/fiber/context.hpp>
#include <boost/fiber/operations.hpp>

#include <liburing.h>

#include <cstring>

MONAD_MPT_NAMESPACE_BEGIN

// Poll write ring for completions and wake any waiting fibers.
// This should be called regularly from the hot loop to process write completions.
// Returns the number of completions processed.
inline size_t poll_write_completions(io_uring *ring)
{
    if (ring == nullptr) {
        return 0;
    }

    size_t count = 0;
    io_uring_cqe *cqe = nullptr;

    // Drain all available completions
    while (io_uring_peek_cqe(ring, &cqe) == 0 && cqe != nullptr) {
        void *user_data = io_uring_cqe_get_data(cqe);
        if (user_data != nullptr) {
            auto *token =
                static_cast<monad::fiber::WriteCompletionToken *>(user_data);
            token->result = cqe->res;
            token->completed = true;

            // Wake up the waiting fiber using standard scheduler
            if (token->waiting_fiber != nullptr) {
                auto *ctx = token->waiting_fiber;
                ctx->get_scheduler()->schedule(ctx);
            }
        }
        io_uring_cqe_seen(ring, cqe);
        ++count;
    }

    return count;
}

// Acquire a write buffer, yielding the fiber if none available.
// This is a fiber-friendly alternative to AsyncIO::get_write_buffer()
// which blocks the thread when buffers are exhausted.
//
// The hot loop polls io_uring completions, which frees buffers as writes
// complete. By yielding, we allow other fibers to run and completions to
// be processed.
//
// @param io The AsyncIO instance to allocate from
// @return A write buffer, guaranteed non-null on return
inline async::AsyncIO::write_buffer_ptr fiber_get_write_buffer(
    async::AsyncIO &io)
{
    while (true) {
        auto buf = io.try_get_write_buffer();
        if (buf) {
            return buf;
        }
        // No buffer available - yield to let hot loop poll completions
        // which may free buffers as writes complete
        boost::this_fiber::yield();
    }
}

// Fiber-based write buffer for accumulating node data and flushing to disk.
// This is a simpler alternative to node_writer_unique_ptr_type that uses
// fiber_write() instead of the sender-receiver pattern.
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
        , buffer_(fiber_get_write_buffer(io))
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

        // Pad to disk page alignment
        constexpr size_t PAGE_SIZE = 4096;
        size_t padded_size = (written_ + PAGE_SIZE - 1) & ~(PAGE_SIZE - 1);
        if (padded_size > written_) {
            std::memset(buffer_.get() + written_, 0, padded_size - written_);
        }

        // Create completion token on stack - valid while fiber is suspended
        monad::fiber::WriteCompletionToken token;
        token.waiting_fiber = boost::fibers::context::active();

        // Submit write via AsyncIO which handles chunk-to-file-offset conversion
        io_->submit_fiber_write(
            std::span<std::byte const>(buffer_.get(), padded_size),
            start_offset_, &token);

        // Yield until completion - hot loop polls io_uring and wakes us
        while (!token.completed) {
            boost::this_fiber::yield();
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
    void flush_and_reset(chunk_offset_t new_offset)
    {
        flush();
        start_offset_ = new_offset;
        // Buffer is reused (still valid after flush)
    }
};

MONAD_MPT_NAMESPACE_END
