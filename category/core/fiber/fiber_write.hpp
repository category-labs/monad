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

#include <category/core/fiber/config.hpp>
#include <category/core/fiber/uring_write_scheduler.hpp>

#include <cstddef>
#include <cstdint>
#include <span>

struct io_uring;

MONAD_FIBER_NAMESPACE_BEGIN

// Result of a fiber write operation
struct WriteResult
{
    int32_t bytes_written{0};
    bool success{false};

    explicit operator bool() const noexcept
    {
        return success;
    }
};

// Submit a write to io_uring and yield the current fiber until completion.
//
// This function:
// 1. Gets an SQE from the ring
// 2. Prepares a write operation
// 3. Submits to io_uring
// 4. Yields the fiber
// 5. Resumes when CQE arrives (via scheduler's poll_completions)
// 6. Returns the result
//
// The buffer must remain valid until the write completes (which it will,
// since it's typically on the fiber's stack or in a buffer pool).
//
// Asserts on io_uring errors (matching current write_operation_io_receiver
// behavior).
//
// @param ring      The io_uring instance to use
// @param fd        File descriptor to write to
// @param buffer    Data to write
// @param offset    File offset for the write
// @param flags     SQE flags (default: IOSQE_FIXED_FILE)
// @return          WriteResult with bytes written and success status
WriteResult fiber_write(
    io_uring *ring,
    int fd,
    std::span<std::byte const> buffer,
    uint64_t offset,
    unsigned flags = 0);

// Submit a write using a registered buffer and yield until completion.
//
// Uses io_uring_prep_write_fixed for writes with pre-registered buffers,
// which can reduce kernel overhead.
//
// @param ring      The io_uring instance to use
// @param fd        File descriptor (registered via io_uring_register_files)
// @param buffer    Data to write (must be from registered buffer pool)
// @param offset    File offset for the write
// @param buf_index Index of the registered buffer
// @return          WriteResult with bytes written and success status
WriteResult fiber_write_registered(
    io_uring *ring,
    int fd,
    std::span<std::byte const> buffer,
    uint64_t offset,
    int buf_index);

MONAD_FIBER_NAMESPACE_END
