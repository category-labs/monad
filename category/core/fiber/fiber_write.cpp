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

#include <category/core/fiber/fiber_write.hpp>

#include <category/core/assert.h>

#include <boost/fiber/operations.hpp>

#include <liburing.h>

#include <cerrno>
#include <cstring>

MONAD_FIBER_NAMESPACE_BEGIN

namespace
{

// Submit to io_uring with EINTR retry
int submit_with_retry(io_uring *ring)
{
    for (;;) {
        int ret = io_uring_submit(ring);
        if (ret >= 0) {
            return ret;
        }
        if (ret == -EINTR) {
            continue;
        }
        // Fatal error - abort with message
        char buffer[256] = "unknown error";
        if (strerror_r(-ret, buffer, sizeof(buffer)) != nullptr) {
            buffer[sizeof(buffer) - 1] = '\0';
        }
        MONAD_ABORT_PRINTF("io_uring_submit failed: %s", buffer);
    }
}

} // namespace

WriteResult fiber_write(
    io_uring *ring,
    int fd,
    std::span<std::byte const> buffer,
    uint64_t offset,
    unsigned flags)
{
    MONAD_ASSERT(ring != nullptr);
    MONAD_ASSERT(!buffer.empty());

    // Prepare completion token on fiber stack
    WriteCompletionToken token;
    token.waiting_fiber = boost::fibers::context::active();

    // Get SQE
    io_uring_sqe *sqe = io_uring_get_sqe(ring);
    if (sqe == nullptr) {
        // Ring is full - this shouldn't happen with properly sized write ring.
        // In future we could yield and retry, but for now assert.
        MONAD_ABORT("io_uring submission queue full");
    }

    // Prepare write
    io_uring_prep_write(
        sqe,
        fd,
        buffer.data(),
        static_cast<unsigned int>(buffer.size()),
        offset);
    sqe->flags |= static_cast<uint8_t>(flags);
    io_uring_sqe_set_data(sqe, &token);

    // Submit
    submit_with_retry(ring);

    // Yield until completion - the scheduler's poll_completions will
    // process the CQE and set token.completed = true
    while (!token.completed) {
        boost::this_fiber::yield();
    }

    // Assert on errors (matches current write_operation_io_receiver behavior)
    MONAD_ASSERT(token.result >= 0, "io_uring write failed");

    return WriteResult{token.result, true};
}

WriteResult fiber_write_registered(
    io_uring *ring,
    int fd,
    std::span<std::byte const> buffer,
    uint64_t offset,
    int buf_index)
{
    MONAD_ASSERT(ring != nullptr);
    MONAD_ASSERT(!buffer.empty());

    // Prepare completion token on fiber stack
    WriteCompletionToken token;
    token.waiting_fiber = boost::fibers::context::active();

    // Get SQE
    io_uring_sqe *sqe = io_uring_get_sqe(ring);
    if (sqe == nullptr) {
        MONAD_ABORT("io_uring submission queue full");
    }

    // Prepare write with registered buffer
    io_uring_prep_write_fixed(
        sqe,
        fd,
        buffer.data(),
        static_cast<unsigned int>(buffer.size()),
        offset,
        buf_index);

    // Use fixed file and IO_DRAIN for ordering (matches existing write pattern)
    sqe->flags |= IOSQE_FIXED_FILE | IOSQE_IO_DRAIN;
    io_uring_sqe_set_data(sqe, &token);

    // Submit
    submit_with_retry(ring);

    // Yield until completion
    while (!token.completed) {
        boost::this_fiber::yield();
    }

    // Assert on errors
    MONAD_ASSERT(token.result >= 0, "io_uring write_fixed failed");

    return WriteResult{token.result, true};
}

MONAD_FIBER_NAMESPACE_END
