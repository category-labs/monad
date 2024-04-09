#pragma once

#include <monad/core/likely.h>
#include <monad/fiber2/config.hpp>
#include <monad/fiber2/dispatcher.hpp>

#include <boost/context/fiber.hpp>

#include <oneapi/tbb/concurrent_priority_queue.h>

#include <cstdint>

MONAD_FIBER_NAMESPACE_BEGIN

namespace detail
{
    struct Task
    {
        int64_t priority{0};
        boost::context::fiber fiber{};
    };

    struct CompareTask
    {
        constexpr bool operator()(Task const &task1, Task const &task2) const
        {
            return task1.priority > task2.priority;
        }
    };

    using Queue = oneapi::tbb::concurrent_priority_queue<Task, CompareTask>;
}

inline thread_local int64_t priority_{0};

static inline detail::Queue queue_{};

void start(int64_t const priority, auto &&f)
{
    boost::context::fiber fiber{
        [f = std::move(f)](boost::context::fiber &&dispatcher) {
            dispatcher_ = std::move(dispatcher).resume();
            f();
            return std::move(dispatcher_);
        }};
    queue_.emplace(priority, std::move(fiber));
}

void dispatch()
{
    detail::Task task;
    if (MONAD_LIKELY(queue_.try_pop(task))) {
        priority_ = task.priority;
        boost::context::fiber fiber{};
        fiber = std::move(task.fiber).resume();
        if (fiber) {
            queue_.emplace(priority_, std::move(fiber));
        }
    }
}

MONAD_FIBER_NAMESPACE_END
