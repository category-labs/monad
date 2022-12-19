#include <monad/fiber/algorithm.hpp>

#include <monad/core/likely.h>

#include <boost/assert.hpp>
#include <boost/fiber/type.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

shared_work::rqueue_type shared_work::rqueue_{};
std::mutex shared_work::rqueue_mtx_{};

shared_work::shared_work()
    : lqueue_{}
{
}

void shared_work::awakened(
    boost::fibers::context *const ctx, fiber_properties &props) noexcept
{
    uint64_t const priority = props.getPriority();
    if (MONAD_UNLIKELY(ctx->is_context(boost::fibers::type::pinned_context))) {
        lqueue_.push_back(*ctx);
    }
    else {
        ctx->detach();
        std::unique_lock<std::mutex> lk{rqueue_mtx_};
        auto it = rqueue_.begin();
        auto const end = rqueue_.end();
        for (; it != end; ++it) {
            if (properties(&*it).getPriority() > priority) {
                break;
            }
        }
        rqueue_.insert(it, *ctx);
    }
}

boost::fibers::context *shared_work::pick_next() noexcept
{
    boost::fibers::context *ctx = nullptr;
    std::unique_lock<std::mutex> lk{rqueue_mtx_};
    if (MONAD_LIKELY(!rqueue_.empty())) {
        ctx = &rqueue_.front();
        rqueue_.pop_front();
        lk.unlock();
        // TODO prefetch as in round_robin?
        BOOST_ASSERT(ctx);
        boost::fibers::context::active()->attach(ctx);
    }
    else {
        lk.unlock();
        if (!lqueue_.empty()) {
            ctx = &lqueue_.front();
            lqueue_.pop_front();
        }
    }
    return ctx;
}

bool shared_work::has_ready_fibers() const noexcept
{
    std::unique_lock<std::mutex> lk{rqueue_mtx_};
    return !rqueue_.empty() || !lqueue_.empty();
}

void shared_work::suspend_until(
    std::chrono::steady_clock::time_point const &) noexcept
{
}

void shared_work::notify() noexcept {}

void shared_work::property_change(
    boost::fibers::context *const ctx, fiber_properties &props) noexcept
{
    if (MONAD_UNLIKELY(ctx->ready_is_linked())) {
        ctx->ready_unlink();
        awakened(ctx, props);
    }
}

MONAD_NAMESPACE_END
