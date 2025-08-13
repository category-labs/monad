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

#include <category/core/fiber/priority_algorithm.hpp>

#include <category/core/likely.h>
#include <category/core/fiber/config.hpp>
#include <category/core/fiber/priority_properties.hpp>
#include <category/core/fiber/priority_queue.hpp>

#include <boost/assert.hpp>
#include <boost/fiber/context.hpp>
#include <boost/fiber/type.hpp>

MONAD_FIBER_NAMESPACE_BEGIN

PriorityAlgorithm::PriorityAlgorithm(
    PriorityQueue &rqueue, bool const prevent_spin)
    : prevent_spin_(prevent_spin)
    , rqueue_{rqueue}

{
}

void PriorityAlgorithm::awakened(
    boost::fibers::context *const ctx, PriorityProperties &) noexcept
{
    if (MONAD_UNLIKELY(ctx->is_context(boost::fibers::type::pinned_context))) {
        lqueue_.push_back(*ctx);
    }
    else {
        ctx->detach();
        rqueue_.push(ctx);
        recent_ = true;
    }
}

context *PriorityAlgorithm::pick_next() noexcept
{
    context *ctx = rqueue_.pop();
    if (prevent_spin_ && !ctx) {
        if (!recent_) {
            std::this_thread::sleep_for(std::chrono::microseconds(10));
        }
        recent_ = false;
    }
    if (MONAD_LIKELY(ctx)) {
        recent_ = true;
        context::active()->attach(ctx);
    }
    else if (!lqueue_.empty()) {
        ctx = &lqueue_.front();
        lqueue_.pop_front();
    }
    return ctx;
}

bool PriorityAlgorithm::has_ready_fibers() const noexcept
{
    if (MONAD_LIKELY(!lqueue_.empty())) {
        return true;
    }
    return !rqueue_.empty();
}

MONAD_FIBER_NAMESPACE_END
