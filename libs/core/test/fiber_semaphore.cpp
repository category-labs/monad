#include <bit>
#include <cstddef>
#include <cstdint>
#include <list>
#include <source_location>

#include <errno.h>
#include <gtest/gtest.h>

#include <monad/config.hpp>
#include <monad/core/c_result.h>
#include <monad/fiber/fiber.h>
#include <monad/fiber/fiber_semaphore.h>
#include <monad/fiber/run_queue.h>

namespace
{
    monad_c_result consumer_fiber_fn(monad_fiber_args_t mfa)
    {
        auto *const sem = std::bit_cast<monad_fiber_semaphore_t *>(mfa.arg[0]);
        std::int64_t count = 0;
        while (true) {
            monad_fiber_semaphore_acquire(sem, MONAD_FIBER_PRIO_NO_CHANGE);
            monad_fiber_yield(monad_c_make_success(count++));
        }
        return monad_c_make_success(0);
    }

}

TEST(fiber_semaphore, serial_basic)
{
    // This tests that interleaving of acquire and release operations are
    // correct using the main thread and a single fiber; it has the same
    // limitations as the `serial_basic` test of fiber_channel
    monad_fiber_t *consumer_fiber;
    monad_run_queue *run_queue;
    monad_fiber_semaphore_t sem;
    monad_fiber_suspend_info_t suspend_info;

    ASSERT_EQ(0, monad_fiber_create(nullptr, &consumer_fiber));
    ASSERT_EQ(0,
        monad_fiber_set_function(
            consumer_fiber,
            MONAD_FIBER_PRIO_HIGHEST,
            consumer_fiber_fn,
            {std::bit_cast<std::uintptr_t>(&sem)}));

    monad_fiber_semaphore_init(&sem);
    ASSERT_EQ(0, monad_run_queue_create(nullptr, 1, &run_queue));

    // Non-blocking acquire from an unsignaled semaphore returns false
    ASSERT_EQ(false, monad_fiber_semaphore_try_acquire(&sem));

    // Put the fiber into a run queue, so that it becomes associated with it.
    // This is what causes subsequent wake-ups to reschedule it there
    ASSERT_EQ(0, monad_run_queue_try_push(run_queue, consumer_fiber));
    ASSERT_EQ(consumer_fiber, monad_run_queue_try_pop(run_queue));

    // Run the fiber until it goes to sleep on the semaphore
    ASSERT_EQ(0, monad_fiber_run(consumer_fiber, &suspend_info));
    ASSERT_EQ(MF_SUSPEND_SLEEP, suspend_info.suspend_type);

    // Because the condition to wake up the fiber has not occurred, the
    // run queue remains empty
    ASSERT_EQ(nullptr, monad_run_queue_try_pop(run_queue));

    // The fiber cannot be run again, because it is busy (on a wait queue)
    ASSERT_EQ(EBUSY, monad_fiber_run(consumer_fiber, &suspend_info));

    // To wake the fiber up, release a wakeup token; this causes the fiber to
    // be re-enqueued on the run queue immediately
    monad_fiber_semaphore_release(&sem, 1);
    ASSERT_EQ(consumer_fiber, monad_run_queue_try_pop(run_queue));

    // Run the consumer, it will wake up and yield an increasing count
    ASSERT_EQ(0, monad_fiber_run(consumer_fiber, &suspend_info));
    ASSERT_EQ(MF_SUSPEND_YIELD, suspend_info.suspend_type);
    ASSERT_TRUE(monad_result_has_value(suspend_info.eval));
    ASSERT_EQ(0, suspend_info.eval.value);

    // The semaphore has no tokens now, release two more tokens into it to
    // verify that the consumer won't sleep when it tries to consume them, but
    // can yield them immediately
    monad_fiber_semaphore_release(&sem, 2);

    // The previous yield puts the fiber back in the run queue; pop it so
    // we don't get EBUSY, then run it and check that it yields again
    // immediately, with no sleep
    ASSERT_EQ(consumer_fiber, monad_run_queue_try_pop(run_queue));
    ASSERT_EQ(0, monad_fiber_run(consumer_fiber, &suspend_info));
    ASSERT_EQ(MF_SUSPEND_YIELD, suspend_info.suspend_type);
    ASSERT_TRUE(monad_result_has_value(suspend_info.eval));
    ASSERT_EQ(1, suspend_info.eval.value);

    // As above, for the second message
    ASSERT_EQ(consumer_fiber, monad_run_queue_try_pop(run_queue));
    ASSERT_EQ(0, monad_fiber_run(consumer_fiber, &suspend_info));
    ASSERT_EQ(MF_SUSPEND_YIELD, suspend_info.suspend_type);
    ASSERT_TRUE(monad_result_has_value(suspend_info.eval));
    ASSERT_EQ(2, suspend_info.eval.value);

    // If run one more time, there are no wakeup tokens available, so we'll
    // sleep
    ASSERT_EQ(consumer_fiber, monad_run_queue_try_pop(run_queue));
    ASSERT_EQ(0, monad_fiber_run(consumer_fiber, &suspend_info));
    ASSERT_EQ(MF_SUSPEND_SLEEP, suspend_info.suspend_type);

    monad_run_queue_destroy(run_queue);
    monad_fiber_destroy(consumer_fiber);
}
