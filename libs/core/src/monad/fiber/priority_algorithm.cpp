#include <monad/fiber/priority_algorithm.hpp>

#include <monad/core/likely.h>
#include <monad/fiber/config.hpp>
#include <monad/fiber/priority_queue.hpp>
#include <monad/fiber/priority_properties.hpp>

#include <boost/assert.hpp>
#include <boost/fiber/context.hpp>
#include <boost/fiber/type.hpp>

MONAD_FIBER_NAMESPACE_BEGIN

PriorityAlgorithm::PriorityAlgorithm(PriorityQueue &rqueue)
    : rqueue_{rqueue}
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
    }
}

context *PriorityAlgorithm::pick_next() noexcept
{
    context *ctx = rqueue_.pop();
    if (MONAD_LIKELY(ctx)) {
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
