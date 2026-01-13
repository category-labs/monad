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

#include <category/core/io/config.hpp>
#include <category/core/likely.h>

#include <boost/fiber/context.hpp>
#include <boost/fiber/scheduler.hpp>

#include <deque>

MONAD_IO_NAMESPACE_BEGIN

class Buffers;

class BufferPool
{
    unsigned char *next_;
    std::deque<boost::fibers::context *> waiters_;

public:
    BufferPool(Buffers const &, bool is_read);

    [[gnu::always_inline]] unsigned char *alloc()
    {
        unsigned char *const next = next_;
        if (next) {
            next_ = *reinterpret_cast<unsigned char **>(next);
        }
        return next;
    }

    [[gnu::always_inline]] unsigned char *alloc_fiber()
    {
        while (true) {
            unsigned char *const next = next_;
            if (MONAD_LIKELY(next)) {
                next_ = *reinterpret_cast<unsigned char **>(next);
                return next;
            }

            // TODO: assert ios_in_flight() ?

            // No buffer: Suspend and wait
            auto *ctx = boost::fibers::context::active();
            waiters_.push_back(ctx);
            ctx->suspend();
        }
    }

    [[gnu::always_inline]] void release(unsigned char *const next)
    {
        *reinterpret_cast<unsigned char **>(next) = next_;
        next_ = next;

        if (!waiters_.empty()) {
            auto *ctx = waiters_.front();
            waiters_.pop_front();
            ctx->get_scheduler()->schedule(ctx);
        }
    }
};

static_assert(sizeof(BufferPool) == 88);
static_assert(alignof(BufferPool) == 8);

MONAD_IO_NAMESPACE_END
