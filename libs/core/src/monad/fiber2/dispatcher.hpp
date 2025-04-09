#pragma once

#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/fiber2/config.hpp>

#include <boost/context/fiber.hpp>
#include <boost/fiber/detail/spinlock.hpp>

#include <condition_variable>
#include <deque>
#include <mutex>
#include <stop_token>
#include <utility>

MONAD_FIBER_NAMESPACE_BEGIN

static inline std::deque<boost::context::fiber> ready_queue_{};
static inline std::mutex ready_queue_mutex_{};
static inline std::condition_variable_any ready_queue_cv_{};
inline thread_local boost::context::fiber dispatcher_{};

void ready_queue_push(boost::context::fiber &&fiber)
{
    {
        std::lock_guard<std::mutex> const lock{ready_queue_mutex_};
        ready_queue_.emplace_back(std::move(fiber));
    }
    ready_queue_cv_.notify_one();
}

boost::context::fiber ready_queue_pop(std::stop_token const &stop_token)
{
    boost::context::fiber fiber{};
    std::unique_lock<std::mutex> lock{ready_queue_mutex_};
    if (ready_queue_cv_.wait(
            lock, stop_token, []() { return !ready_queue_.empty(); })) {
        fiber = std::move(ready_queue_.front());
        ready_queue_.pop_front();
    }
    return fiber;
}

boost::context::fiber ready_queue_pop_try()
{
    boost::context::fiber fiber{};
    std::lock_guard<std::mutex> const lock{ready_queue_mutex_};
    if (!ready_queue_.empty()) {
        fiber = std::move(ready_queue_.front());
        ready_queue_.pop_front();
    }
    return fiber;
}

void run(std::stop_token const stop_token)
{
    while (!stop_token.stop_requested()) {
        auto fiber = ready_queue_pop(stop_token);
        if (MONAD_LIKELY(fiber)) {
            MONAD_ASSERT(!dispatcher_);
            MONAD_ASSERT(!std::move(fiber).resume_with(
                [](boost::context::fiber &&dispatcher) {
                    dispatcher_ = std::move(dispatcher);
                    return boost::context::fiber{};
                }));
        }
    }
}

void start(auto &&f)
{
    boost::context::fiber fiber{
        [f = std::move(f)](boost::context::fiber &&/*dispatcher*/) {
            //dispatcher_ = std::move(dispatcher).resume();
            f();
            return std::move(dispatcher_);
        }};
    ready_queue_push(std::move(fiber));
}

void yield()
{
    MONAD_ASSERT(dispatcher_);
    MONAD_ASSERT(!std::move(dispatcher_)
                      .resume_with([](boost::context::fiber &&this_fiber) {
                          ready_queue_push(std::move(this_fiber));
                          return boost::context::fiber{};
                      }));
}

class Future
{
    using Mutex = boost::fibers::detail::spinlock;
    using Lock = std::unique_lock<Mutex>;

    Mutex mutex_{};
    bool flag_{false};
    boost::context::fiber fiber_{};

public:
    void wait()
    {
        MONAD_ASSERT(dispatcher_);
        MONAD_ASSERT(!fiber_);

        {
            std::lock_guard<Mutex> const lock{mutex_};
            if (flag_) {
                return;
            }
        }

        boost::context::fiber next_fiber = ready_queue_pop_try();
        if (!next_fiber) {
            next_fiber = std::move(dispatcher_);
        }

        MONAD_ASSERT(
            !std::move(next_fiber)
                 .resume_with([this](boost::context::fiber &&this_fiber) {
                     Lock const lock{mutex_};
                     if (!flag_) {
                         fiber_ = std::move(this_fiber);
                     }
                     else {
                         ready_queue_push(std::move(this_fiber));
                     }
                     return boost::context::fiber{};
                 }));
    }

    void set_value()
    {
        Lock const lock{mutex_};
        MONAD_ASSERT(!flag_);
        flag_ = true;
        if (fiber_) {
            ready_queue_push(std::move(fiber_));
        }
    }
};

MONAD_FIBER_NAMESPACE_END
