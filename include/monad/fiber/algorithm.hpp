#pragma once

#include <monad/config.hpp>
#include <monad/fiber/properties.hpp>

#include <boost/fiber/algo/algorithm.hpp>
#include <boost/fiber/context.hpp>
#include <boost/fiber/scheduler.hpp>

#include <chrono>
#include <mutex>

MONAD_NAMESPACE_BEGIN

class shared_work final
    : public boost::fibers::algo::algorithm_with_properties<fiber_properties>
{
    using rqueue_type = boost::fibers::scheduler::ready_queue_type;
    using lqueue_type = boost::fibers::scheduler::ready_queue_type;

    static rqueue_type rqueue_;
    static std::mutex rqueue_mtx_; // TODO use spin lock

    lqueue_type lqueue_;

public:
    shared_work();

    shared_work(shared_work const &) = delete;
    shared_work(shared_work &&) = delete;

    shared_work &operator=(shared_work const &) = delete;
    shared_work &operator=(shared_work &&) = delete;

    void
    awakened(boost::fibers::context *, fiber_properties &) noexcept override;

    boost::fibers::context *pick_next() noexcept override;

    bool has_ready_fibers() const noexcept override;

    void suspend_until(
        std::chrono::steady_clock::time_point const &) noexcept override;

    void notify() noexcept override;

    void property_change(
        boost::fibers::context *, fiber_properties &) noexcept override;
};

MONAD_NAMESPACE_END
