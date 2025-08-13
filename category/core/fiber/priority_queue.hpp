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

#include <category/core/assert.h>
#include <category/core/likely.h>
#include <category/core/fiber/config.hpp>
#include <category/core/fiber/priority_properties.hpp>

#include <boost/fiber/context.hpp>

#include <oneapi/tbb/concurrent_priority_queue.h>

MONAD_FIBER_NAMESPACE_BEGIN

using boost::fibers::context;

class PriorityQueue final
{
    struct Compare
    {
        static constexpr uint64_t get_priority(context const *const ctx)
        {
            auto const *const properties =
                static_cast<PriorityProperties const *>(ctx->get_properties());
            MONAD_ASSERT(properties); // TODO debug assert
            return properties->get_priority();
        }

        constexpr bool
        operator()(context const *const ctx1, context const *const ctx2)
        {
            return get_priority(ctx1) > get_priority(ctx2);
        }
    };

    oneapi::tbb::concurrent_priority_queue<context *, Compare> queue_;

public:
    bool empty() const;

    context *pop();

    void push(context *);
};

MONAD_FIBER_NAMESPACE_END
