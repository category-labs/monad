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

#include <category/core/fiber/uring_write_scheduler.hpp>

#include <category/core/assert.h>

#include <liburing.h>

MONAD_FIBER_NAMESPACE_BEGIN

UringWriteFiberScheduler::UringWriteFiberScheduler(io_uring *wr_ring)
    : wr_ring_(wr_ring)
    , main_cntx_(context::active())
{
    MONAD_ASSERT(wr_ring_ != nullptr);
    MONAD_ASSERT(main_cntx_ != nullptr);
    MONAD_ASSERT(main_cntx_->is_context(boost::fibers::type::main_context));
    current_scheduler = this;
}

void UringWriteFiberScheduler::awakened(
    context *ctx, WriteProperties & /*props*/) noexcept
{
    MONAD_DEBUG_ASSERT(ctx != nullptr);
    MONAD_DEBUG_ASSERT(!ctx->ready_is_linked());

    if (ctx->is_context(boost::fibers::type::dispatcher_context)) {
        // Dispatcher context - just add to queue
        ctx->ready_link(ready_queue_);
        return;
    }

    ++ready_cnt_;

    if (ctx == main_cntx_) {
        // The io loop fiber is being awakened
        flags_.ioloop_woke = 1;
    }

    ctx->ready_link(ready_queue_);
}

context *UringWriteFiberScheduler::pick_next() noexcept
{
    // During shutdown, just return nullptr to let Boost.Fiber clean up
    if (done_) {
        return nullptr;
    }

    // NOTE: We intentionally do NOT poll io_uring here.
    // The hot loop in rwdb_run() is responsible for calling poll_completions().
    // This keeps the scheduler simple and avoids io_uring access during TLS cleanup.

    if (ready_queue_.empty()) {
        return nullptr;
    }

    context *ctx = nullptr;

    // Prioritize io loop fiber when it was explicitly woken
    if (flags_.ioloop_woke && main_cntx_ != nullptr &&
        main_cntx_->ready_is_linked()) {
        ctx = main_cntx_;
        ctx->ready_unlink();
        flags_.ioloop_woke = 0;
    } else {
        ctx = &ready_queue_.front();
        ready_queue_.pop_front();

        if (flags_.ioloop_suspended) {
            flags_.ioloop_yielded = 1;
        }
    }

    if (!ctx->is_context(boost::fibers::type::dispatcher_context)) {
        --ready_cnt_;
    }

    return ctx;
}

bool UringWriteFiberScheduler::has_ready_fibers() const noexcept
{
    return ready_cnt_ > 0;
}

void UringWriteFiberScheduler::suspend_until(
    std::chrono::steady_clock::time_point const & /*abs_time*/) noexcept
{
    // Called by dispatcher when no fibers are ready.
    // We cannot poll io_uring here because the completion queue may contain
    // sender-receiver completions with incompatible user_data. Polling must
    // be done by code that knows what completions to expect.
    flags_.suspenduntil_called = 1;

    if (done_) {
        return;
    }

    // Schedule main context to run so caller can poll completions
    if (main_cntx_ != nullptr && !main_cntx_->ready_is_linked()) {
        main_cntx_->ready_link(ready_queue_);
        ++ready_cnt_;
    }
}

void UringWriteFiberScheduler::notify() noexcept
{
    // Called from other threads to wake the scheduler.
    // In our single-threaded write model, this is mostly a no-op.
    // If we need cross-thread notification in the future, we could
    // use eventfd registered with io_uring.
}

size_t UringWriteFiberScheduler::poll_completions(bool blocking)
{
    if (wr_ring_ == nullptr || done_) {
        return 0;
    }

    size_t count = 0;
    io_uring_cqe *cqe = nullptr;

    if (blocking) {
        // Wait for at least one completion
        int ret = io_uring_wait_cqe(wr_ring_, &cqe);
        if (ret == 0 && cqe != nullptr) {
            process_cqe(cqe);
            io_uring_cqe_seen(wr_ring_, cqe);
            ++count;
        }
    }

    // Drain all available completions
    while (io_uring_peek_cqe(wr_ring_, &cqe) == 0 && cqe != nullptr) {
        process_cqe(cqe);
        io_uring_cqe_seen(wr_ring_, cqe);
        ++count;
    }

    return count;
}

void UringWriteFiberScheduler::process_cqe(io_uring_cqe *cqe)
{
    MONAD_DEBUG_ASSERT(cqe != nullptr);

    void *user_data = io_uring_cqe_get_data(cqe);
    if (user_data == nullptr) {
        // No associated token - could be a cancelled operation
        return;
    }

    auto *token = static_cast<WriteCompletionToken *>(user_data);
    token->result = cqe->res;
    token->completed = true;

    // Wake up the waiting fiber
    if (token->waiting_fiber != nullptr) {
        context *ctx = token->waiting_fiber;
        // Schedule the fiber to run. This adds it to the scheduler's ready
        // queue via awakened().
        ctx->get_scheduler()->schedule(ctx);
    }
}

MONAD_FIBER_NAMESPACE_END
