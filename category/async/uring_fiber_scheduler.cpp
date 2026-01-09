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

#include <category/async/uring_fiber_scheduler.hpp>

#include <category/async/io.hpp>
#include <category/core/assert.h>

MONAD_FIBER_NAMESPACE_BEGIN

UringFiberScheduler::UringFiberScheduler(monad::async::AsyncIO *io)
    : io_(io)
{
    MONAD_ASSERT(io_ != nullptr);
}

void UringFiberScheduler::awakened(
    context *ctx, FiberProperties & /*props*/) noexcept
{
    MONAD_DEBUG_ASSERT(ctx != nullptr);
    MONAD_DEBUG_ASSERT(!ctx->ready_is_linked());

    if (!ctx->is_context(boost::fibers::type::dispatcher_context)) {
        ++ready_cnt_;
    }

    ctx->ready_link(ready_queue_);
}

context *UringFiberScheduler::pick_next() noexcept
{
    if (ready_queue_.empty()) {
        return nullptr;
    }

    context *ctx = &ready_queue_.front();
    ready_queue_.pop_front();

    if (!ctx->is_context(boost::fibers::type::dispatcher_context)) {
        --ready_cnt_;
    }

    return ctx;
}

bool UringFiberScheduler::has_ready_fibers() const noexcept
{
    return ready_cnt_ > 0;
}

void UringFiberScheduler::suspend_until(
    std::chrono::steady_clock::time_point const & /*abs_time*/) noexcept
{
    io_->poll_nonblocking();
}

void UringFiberScheduler::notify() noexcept
{
    // No-op for single-threaded usage
}

MONAD_FIBER_NAMESPACE_END
