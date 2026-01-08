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

UringFiberScheduler::UringFiberScheduler(io_uring *rd_ring, io_uring *wr_ring)
    : rd_ring_(rd_ring)
    , wr_ring_(wr_ring)
{
    MONAD_ASSERT(rd_ring_ != nullptr);
    MONAD_ASSERT(wr_ring_ != nullptr);
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
    // Poll both rings for completions
    size_t completions = poll_single_ring(rd_ring_);
    if (wr_ring_ != rd_ring_) {
        completions += poll_single_ring(wr_ring_);
    }

    if (completions == 0) {
        // No completions ready - wait briefly on each ring
        wait_on_ring(rd_ring_);
        if (wr_ring_ != rd_ring_) {
            wait_on_ring(wr_ring_);
        }
    }
}

void UringFiberScheduler::notify() noexcept
{
    // Called from other threads to wake the scheduler.
    // In the current single-threaded upsert model, this is a no-op.
}

size_t UringFiberScheduler::poll_single_ring(io_uring *ring)
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
            // Check magic number to ensure this is a fiber completion.
            // Other completions (e.g., sender-receiver) have different user_data.
            auto *token = static_cast<CompletionToken *>(user_data);
            if (token->magic == CompletionToken::FIBER_COMPLETION_MAGIC) {
                token->result = cqe->res;
                token->completed = true;

                // Wake up the waiting fiber
                if (token->waiting_fiber != nullptr &&
                    !token->waiting_fiber->ready_is_linked()) {
                    auto *ctx = token->waiting_fiber;
                    ctx->get_scheduler()->schedule(ctx);
                }
            }
            // Non-fiber completions are left for other code to process
        }
        io_uring_cqe_seen(ring, cqe);
        ++count;
    }

    return count;
}

bool UringFiberScheduler::wait_on_ring(io_uring *ring)
{
    if (ring == nullptr) {
        return false;
    }

    io_uring_cqe *cqe = nullptr;
    struct __kernel_timespec ts = {.tv_sec = 0, .tv_nsec = 100000}; // 100us

    int ret = io_uring_wait_cqe_timeout(ring, &cqe, &ts);
    if (ret == 0 && cqe != nullptr) {
        void *user_data = io_uring_cqe_get_data(cqe);
        if (user_data != nullptr) {
            auto *token = static_cast<CompletionToken *>(user_data);
            if (token->magic == CompletionToken::FIBER_COMPLETION_MAGIC) {
                token->result = cqe->res;
                token->completed = true;

                if (token->waiting_fiber != nullptr &&
                    !token->waiting_fiber->ready_is_linked()) {
                    token->waiting_fiber->get_scheduler()->schedule(
                        token->waiting_fiber);
                }
            }
        }
        io_uring_cqe_seen(ring, cqe);
        return true;
    }

    return false;
}

MONAD_FIBER_NAMESPACE_END
