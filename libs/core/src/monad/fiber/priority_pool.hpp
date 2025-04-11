#pragma once

#include <monad/fiber/config.hpp>
#include <monad/fiber/priority_queue.hpp>
#include <monad/fiber/priority_task.hpp>

#include <boost/fiber/buffered_channel.hpp>
#include <boost/fiber/condition_variable.hpp>
#include <boost/fiber/mutex.hpp>

#include <future>
#include <thread>
#include <utility>

MONAD_FIBER_NAMESPACE_BEGIN

class PriorityPool final
{
    PriorityQueue queue_{};

    bool done_{false};

    boost::fibers::mutex mutex_{};
    boost::fibers::condition_variable cv_{};

    std::vector<std::thread> threads_{};

    boost::fibers::buffered_channel<PriorityTask> channel_{1024};

    std::vector<boost::fibers::fiber> fibers_{};

    std::promise<void> start_{};

public:
    PriorityPool(
        unsigned n_threads, unsigned n_fibers, bool prevent_spin = false);

    PriorityPool(PriorityPool const &) = delete;
    PriorityPool &operator=(PriorityPool const &) = delete;

    ~PriorityPool();

    void submit(uint64_t const priority, std::function<void()> task)
    {
        channel_.push({priority, std::move(task)});
    }
};

MONAD_FIBER_NAMESPACE_END
