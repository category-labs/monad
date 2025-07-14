#include <category/core/fiber/priority_queue.hpp>

#include <category/core/fiber/config.hpp>

MONAD_FIBER_NAMESPACE_BEGIN

bool PriorityQueue::empty() const
{
    return queue_.empty();
}

context *PriorityQueue::pop()
{
    context *ctx = nullptr;
    queue_.try_pop(ctx);
    return ctx;
}

void PriorityQueue::push(context *const ctx)
{
    queue_.push(ctx);
}

MONAD_FIBER_NAMESPACE_END
