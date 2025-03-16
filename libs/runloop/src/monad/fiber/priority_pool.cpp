#include <monad/fiber/priority_pool.hpp>

#include <monad/core/assert.h>
#include <monad/core/spinlock.h>
#include <monad/core/spinloop.h>
#include <monad/fiber/config.hpp>
#include <monad/fiber/fiber.h>
#include <monad/fiber/fiber_channel.h>
#include <monad/fiber/run_queue.h>

#include <atomic>
#include <bit>
#include <cstdio>
#include <memory>
#include <system_error>
#include <thread>
#include <utility>

#include <pthread.h>

namespace
{

    // Typical Ethereum execution does not use much stack space, but there are
    // some pathological cases such as this monad_ethereum_test test case:
    //
    //   BlockchainTests.GeneralStateTests/stCallCreateCallCodeTest/Call1024BalanceTooLow.json
    //
    // This requires slightly less than 4 MiB for most build types and
    // compilers, but the combination of clang+debug pushes it to require 8 MiB.
    // If this ends up mattering we can add split-stack support later.
    constexpr size_t FIBER_STACK_SIZE = (1 << 23); // 8 MiB

    // The work-stealing function run by all the fibers. It pulls TaskChannelMsg
    // objects from the task fiber channel and runs their PriorityTasks
    [[noreturn]] monad_c_result fiber_worker_main(monad_fiber_args_t mfa)
    {
        using monad::fiber::TaskChannelMsg;
        auto *const task_channel = std::bit_cast<monad_fiber_channel_t *>(mfa.arg[0]);
        while (true) {
            // Pop a message header from the fiber channel. This describes a
            // a TaskChannelMsg::Payload object
            monad_fiber_msghdr_t *const hdr =
                monad_fiber_channel_pop(task_channel, MONAD_FIBER_PRIO_LOWEST);
            MONAD_ASSERT(
                hdr->msg_buf.iov_len == sizeof(TaskChannelMsg::Payload));
            auto *const payload =
                static_cast<TaskChannelMsg::Payload *>(hdr->msg_buf.iov_base);

            // Set our fiber priority to whatever the task tells us it's
            // supposed to be, then run the task
            monad_fiber_self()->priority = payload->prio_task.priority;
            payload->prio_task.task();

            // Tell the pool we're done with the task
            payload->pool->finish(payload->i_msg);
        }
    }

} // anonymous namespace

MONAD_FIBER_NAMESPACE_BEGIN

PriorityPool::PriorityPool(unsigned const n_threads, unsigned const n_fibers)
{
    MONAD_ASSERT(n_threads > 0);
    MONAD_ASSERT(n_fibers > 0);

    threads_.reserve(n_threads);
    if (int const rc = monad_run_queue_create(nullptr, n_fibers, &run_queue_)) {
        throw std::system_error{
            rc, std::generic_category(), "monad_run_queue_create failed"};
    }
    monad_fiber_channel_init(&task_channel_);
    monad_spinlock_init(&channel_msgs_lock_);

    // Initialize our pool of fibers: set them to run the work-stealing
    // algorithm, and add them to the run queue
    char namebuf[MONAD_FIBER_NAME_LEN + 1];
    monad_fiber_attr_t const fiber_attr = {
        .stack_size = FIBER_STACK_SIZE, .alloc = nullptr};
    for (unsigned i = 0; i < n_fibers; ++i) {
        monad_fiber_t *&fiber = fibers_.emplace_back();
        monad_fiber_create(&fiber_attr, &fiber);
        monad_fiber_set_function(
            fiber,
            MONAD_FIBER_PRIO_LOWEST,
            fiber_worker_main,
            {std::bit_cast<uintptr_t>(&task_channel_)});
        snprintf(namebuf, sizeof namebuf, "F%03d", i);
        (void)monad_fiber_set_name(fiber, namebuf);
        int const rc = monad_run_queue_try_push(run_queue_, fiber);
        MONAD_ASSERT(rc == 0); // Run queue should always be big enough
    }

    // Initialize the worker threads that host fibers
    for (unsigned i = 0; i < n_threads; ++i) {
        auto thread = std::thread([this, i] {
            char name[16];
            int rc;
            std::snprintf(name, sizeof name, "worker_%02u", i);
            pthread_setname_np(pthread_self(), name);
            while (!done_.load(std::memory_order_acquire)) {
                // Get the highest priority fiber ready to run
                monad_fiber_t *const fiber =
                    monad_run_queue_try_pop(run_queue_);
                if (fiber == nullptr) {
                    monad_spinloop_hint();
                    continue; // Nothing is ready to run
                }

                // Run the fiber until it suspends; the work-stealing fibers
                // never return
                rc = monad_fiber_run(fiber, nullptr);
                MONAD_ASSERT(rc == 0);
            }
        });
        threads_.push_back(std::move(thread));
    }
}

PriorityPool::~PriorityPool()
{
    done_ = true;
    while (threads_.size()) {
        auto &thread = threads_.back();
        thread.join();
        threads_.pop_back();
    }
    monad_run_queue_destroy(run_queue_);
    for (monad_fiber_t *fiber : fibers_) {
        monad_fiber_destroy(fiber);
    }
}

void PriorityPool::submit(
    monad_fiber_prio_t priority, std::function<void()> task)
{
    MONAD_SPINLOCK_LOCK(&channel_msgs_lock_);
    TaskChannelMsg &channel_msg = channel_msgs_.emplace_back(
        monad_fiber_msghdr_t{},
        TaskChannelMsg::Payload{
            this, PriorityTask{priority, std::move(task)}, {}});
    channel_msg.payload.i_msg = --channel_msgs_.end();
    MONAD_SPINLOCK_UNLOCK(&channel_msgs_lock_);
    monad_fiber_msghdr_init_trailing(
        &channel_msg.hdr, sizeof channel_msg.payload);
    monad_fiber_channel_push(&task_channel_, &channel_msg.hdr);
}

MONAD_FIBER_NAMESPACE_END
