#pragma once

#include <monad/core/spinlock.h>
#include <monad/fiber/config.hpp>
#include <monad/fiber/fiber.h>
#include <monad/fiber/fiber_channel.h>
#include <monad/fiber/priority_task.hpp>
#include <monad/fiber/run_queue.h>

#include <atomic>
#include <functional>
#include <list>
#include <thread>
#include <utility>
#include <vector>

MONAD_FIBER_NAMESPACE_BEGIN

class PriorityPool;

// A PriorityTask, plus additional book-keeping fields to help manage its memory
// and allow it to be linked onto a fiber channel
struct TaskChannelMsg
{
    using token_t = std::list<TaskChannelMsg>::const_iterator;

    monad_fiber_msghdr_t hdr; ///< msg header to link us onto a channel

    struct Payload
    {
        PriorityPool *pool; ///< Pool we live in
        PriorityTask prio_task; ///< The task itself
        token_t i_msg; ///< Ref to the TaskChannelMsg, from pool perspective
    } payload;
};

class PriorityPool final
{
    monad_run_queue_t *run_queue_{};
    monad_fiber_channel_t task_channel_{};
    std::vector<std::thread> threads_{};
    std::vector<monad_fiber_t *> fibers_{};
    std::atomic<bool> done_{false};

    alignas(64) monad_spinlock_t channel_msgs_lock_;
    std::list<TaskChannelMsg> channel_msgs_;

public:
    PriorityPool(unsigned n_threads, unsigned n_fibers);

    PriorityPool(PriorityPool const &) = delete;
    PriorityPool &operator=(PriorityPool const &) = delete;

    ~PriorityPool();

    // Submit a task to the fiber pool
    void submit(monad_fiber_prio_t priority, std::function<void()> task);

    // Called by the fiber to mark that the task is finished
    void finish(TaskChannelMsg::token_t finished)
    {
        MONAD_SPINLOCK_LOCK(&channel_msgs_lock_);
        channel_msgs_.erase(finished); // Reclaim the memory
        MONAD_SPINLOCK_UNLOCK(&channel_msgs_lock_);
    }
};

MONAD_FIBER_NAMESPACE_END
