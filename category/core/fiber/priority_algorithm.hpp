#pragma once

#include <category/core/fiber/config.hpp>
#include <category/core/fiber/priority_properties.hpp>
#include <category/core/fiber/priority_queue.hpp>

#include <boost/fiber/algo/algorithm.hpp>
#include <boost/fiber/context.hpp>
#include <boost/fiber/scheduler.hpp>

#include <chrono>

MONAD_FIBER_NAMESPACE_BEGIN

using boost::fibers::context;

class PriorityAlgorithm final
    : public boost::fibers::algo::algorithm_with_properties<PriorityProperties>
{
    bool recent_{true};
    // if set true, threads do not spin when no fiber available
    bool prevent_spin_{false};

    PriorityQueue &rqueue_;

    using lqueue_type = boost::fibers::scheduler::ready_queue_type;

    lqueue_type lqueue_{};

public:
    explicit PriorityAlgorithm(PriorityQueue &, bool prevent_spin = false);

    PriorityAlgorithm(PriorityAlgorithm const &) = delete;
    PriorityAlgorithm(PriorityAlgorithm &&) = delete;

    PriorityAlgorithm &operator=(PriorityAlgorithm const &) = delete;
    PriorityAlgorithm &operator=(PriorityAlgorithm &&) = delete;

    void awakened(context *, PriorityProperties &) noexcept override;

    context *pick_next() noexcept override;

    bool has_ready_fibers() const noexcept override;

    void suspend_until(
        std::chrono::steady_clock::time_point const &) noexcept override
    {
    }

    void notify() noexcept override {}
};

MONAD_FIBER_NAMESPACE_END
