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
#include <monad/fiber/fiber_channel.h>
#include <monad/fiber/run_queue.h>

namespace
{
    // A message passed between threads
    struct message
    {
        monad_fiber_msghdr_t header; ///< Linkage for channel

        struct payload_t
        {
            std::int64_t secret; ///< Message content (a secret number)
            std::list<message>::const_iterator i_self; ///< Iterator to our node
        } payload;
    };

    struct channel_test_state
    {
        monad_fiber_channel_t channel;
        std::list<message> messages;

        void push_message(std::int64_t secret)
        {
            message &msg = messages.emplace_back();
            monad_fiber_msghdr_init_trailing(&msg.header, sizeof msg.payload);
            msg.payload.secret = secret;
            msg.payload.i_self = --messages.end();
            monad_fiber_channel_push(&channel, &msg.header);
        }
    };

    monad_c_result consumer_fiber_fn(monad_fiber_args_t mfa)
    {
        auto *const state = std::bit_cast<channel_test_state *>(mfa.arg[0]);
        while (true) {
            monad_fiber_msghdr_t *const msghdr = monad_fiber_channel_pop(
                &state->channel, MONAD_FIBER_PRIO_NO_CHANGE);
            message::payload_t *const mp =
                std::bit_cast<message::payload_t *>(msghdr->msg_buf.iov_base);
            std::int64_t const secret = mp->secret; // Copy before destroying mp
            state->messages.erase(mp->i_self);
            monad_fiber_yield(monad_c_make_success(secret));
        }
        return monad_c_make_success(0);
    }

}

TEST(fiber_channel, serial_basic)
{
    // This tests that interleaving of push and pop operations are correct
    // using the main thread and a single fiber, so this test is too simple to
    // check the multithreaded correctness of the implementation (it is not
    // subject to multithreaded race conditions).
    monad_fiber_t *consumer_fiber;
    monad_run_queue *run_queue;
    channel_test_state state;
    monad_fiber_suspend_info_t suspend_info;

    ASSERT_EQ(0, monad_fiber_create(nullptr, &consumer_fiber));
    ASSERT_EQ(0,
        monad_fiber_set_function(
            consumer_fiber,
            MONAD_FIBER_PRIO_HIGHEST,
            consumer_fiber_fn,
            {std::bit_cast<std::uintptr_t>(&state)}));

    monad_fiber_channel_init(&state.channel);
    ASSERT_EQ(0, monad_run_queue_create(nullptr, 1, &run_queue));

    // Non-blocking pop from an empty channel returns nullptr
    ASSERT_EQ(nullptr, monad_fiber_channel_try_pop(&state.channel));

    // Put the fiber into a run queue, so that it becomes associated with it.
    // This is what causes subsequent wake-ups to reschedule it there
    ASSERT_EQ(0, monad_run_queue_try_push(run_queue, consumer_fiber));
    ASSERT_EQ(consumer_fiber, monad_run_queue_try_pop(run_queue));

    // Run the fiber until it goes to sleep on the channel
    ASSERT_EQ(0, monad_fiber_run(consumer_fiber, &suspend_info));
    ASSERT_EQ(MF_SUSPEND_SLEEP, suspend_info.suspend_type);

    // Because the condition to wake up the fiber has not occurred, the
    // run queue remains empty
    ASSERT_EQ(nullptr, monad_run_queue_try_pop(run_queue));

    // The fiber cannot be run again, because it is busy (on a wait queue)
    ASSERT_EQ(EBUSY, monad_fiber_run(consumer_fiber, &suspend_info));

    // To wake the fiber up, push a message; this causes the fiber to be
    // re-enqueued on the run queue immediately
    state.push_message(33);
    ASSERT_EQ(consumer_fiber, monad_run_queue_try_pop(run_queue));

    // Run the consumer, it will wake up and yield the secret
    ASSERT_EQ(0, monad_fiber_run(consumer_fiber, &suspend_info));
    ASSERT_EQ(MF_SUSPEND_YIELD, suspend_info.suspend_type);
    ASSERT_TRUE(monad_result_has_value(suspend_info.eval));
    ASSERT_EQ(33, suspend_info.eval.value);

    // The channel is empty now, put two more values into it to verify that
    // the consumer won't sleep when it tries to consume them, but can yield
    // them immediately
    state.push_message(100);
    state.push_message(200);

    // The previous yield puts the fiber back in the run queue; pop it so
    // we don't get EBUSY, then run it and check that it yields again
    // immediately, with no sleep
    ASSERT_EQ(consumer_fiber, monad_run_queue_try_pop(run_queue));
    ASSERT_EQ(0, monad_fiber_run(consumer_fiber, &suspend_info));
    ASSERT_EQ(MF_SUSPEND_YIELD, suspend_info.suspend_type);
    ASSERT_TRUE(monad_result_has_value(suspend_info.eval));
    ASSERT_EQ(100, suspend_info.eval.value);

    // As above, for the second message
    ASSERT_EQ(consumer_fiber, monad_run_queue_try_pop(run_queue));
    ASSERT_EQ(0, monad_fiber_run(consumer_fiber, &suspend_info));
    ASSERT_EQ(MF_SUSPEND_YIELD, suspend_info.suspend_type);
    ASSERT_TRUE(monad_result_has_value(suspend_info.eval));
    ASSERT_EQ(200, suspend_info.eval.value);

    // If run one more time, there are no messages waiting, so we'll sleep
    ASSERT_EQ(consumer_fiber, monad_run_queue_try_pop(run_queue));
    ASSERT_EQ(0, monad_fiber_run(consumer_fiber, &suspend_info));
    ASSERT_EQ(MF_SUSPEND_SLEEP, suspend_info.suspend_type);

    monad_run_queue_destroy(run_queue);
    monad_fiber_destroy(consumer_fiber);
}
