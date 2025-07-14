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
