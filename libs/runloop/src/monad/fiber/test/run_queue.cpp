#include <random>
#include <unordered_set>
#include <vector>

#include <errno.h>
#include <gtest/gtest.h>

#include <monad/fiber/fiber.h>
#include <monad/fiber/run_queue.h>

static monad_c_result dummy_function(monad_fiber_args_t)
{
    return monad_c_make_success(0);
}

TEST(run_queue, basic_test)
{
    constexpr std::size_t NumberOfFibers = 256;
    constexpr std::size_t NumberOfTrials = 2048;
    std::vector<monad_fiber_t *> fibers;
    monad_run_queue_t *rq;

    for (std::size_t i = 0; i < NumberOfFibers; ++i) {
        auto &fiber = fibers.emplace_back();
        ASSERT_EQ(0, monad_fiber_create(nullptr, &fiber));

        // Install a dummy function for the fiber; if we don't do this, the
        // run queue will think it is not in a runnable state, and would return
        // ENXIO
        auto const prio = static_cast<monad_fiber_prio_t>(i);
        ASSERT_EQ(0, monad_fiber_set_function(fiber, prio, dummy_function, {}));
    }
    ASSERT_EQ(0, monad_run_queue_create(nullptr, NumberOfFibers, &rq));
    std::default_random_engine rand_engine{std::random_device{}()};
    std::uniform_int_distribution prio_dist{
        MONAD_FIBER_PRIO_HIGHEST, MONAD_FIBER_PRIO_LOWEST};

    for (std::size_t i = 0; i < NumberOfTrials; ++i) {
        // A trial is an assignment of a random priority to all fibers, followed
        // by their insertion into the priority queue. Then we check that the
        // popped sequence is always in priority order.
        ASSERT_TRUE(monad_run_queue_is_empty(rq));

        for (auto *fiber : fibers) {
            fiber->priority = prio_dist(rand_engine);
            ASSERT_EQ(0, monad_run_queue_try_push(rq, fiber));
        }

        // Verify that we aren't allowed to overflow the queue
        ASSERT_EQ(ENOBUFS, monad_run_queue_try_push(rq, fibers.front()));

        monad_fiber_prio_t last_prio = MONAD_FIBER_PRIO_HIGHEST;
        while (!monad_run_queue_is_empty(rq)) {
            monad_fiber_t *const fiber = monad_run_queue_try_pop(rq);
            ASSERT_NE(nullptr, fiber);
            // The last priority always has higher (or equal) priority than
            // the next one we're going to run. A higher priority is represented
            // by a smaller number, so >= priority is <= numerically.
            ASSERT_LE(last_prio, fiber->priority);
            last_prio = fiber->priority;
        }

        // When empty, pop nullptr
        ASSERT_EQ(nullptr, monad_run_queue_try_pop(rq));
    }

    monad_run_queue_destroy(rq);
    for (auto *fiber : fibers) {
        monad_fiber_destroy(fiber);
    }
}

#if MONAD_FIBER_RUN_QUEUE_SUPPORT_EQUAL_PRIO

TEST(run_queue, equal_round_robin)
{
    constexpr std::size_t NumberOfFibers = 128;

    std::vector<monad_fiber_t *> fibers;
    monad_run_queue_t *rq;

    for (std::size_t i = 0; i < NumberOfFibers; ++i) {
        auto &fiber = fibers.emplace_back();
        ASSERT_EQ(0, monad_fiber_create(nullptr, &fiber));

        // Install a dummy function for the fiber; if we don't do this, the
        // run queue will think it is not in a runnable state, and would return
        // ENXIO
        ASSERT_EQ(
            0,
            monad_fiber_set_function(
                fiber, MONAD_FIBER_PRIO_HIGHEST, dummy_function, {}));
    }
    ASSERT_EQ(0, monad_run_queue_create(nullptr, NumberOfFibers, &rq));

    // The round-robin test checks that equal priority fibers are considered
    // to have lower priority upon reinsertion into the priority queue. If this
    // were not the case, and we had two fibers F1 and F2 with the same
    // priority P, we might never run F2. Popping F1 and re-enqueuing it could
    // return F1 every time, and we will never have a chance to run F2.
    for (std::size_t i = 0; i < NumberOfFibers; ++i) {
        ASSERT_EQ(0, monad_run_queue_try_push(rq, fibers[i]));
    }

    std::unordered_set<monad_fiber_t *> seen_fibers;
    for (std::size_t i = 0; i < NumberOfFibers; ++i) {
        monad_fiber_t *const fiber = monad_run_queue_try_pop(rq);

        // Check that we haven't seen this fiber before
        ASSERT_FALSE(seen_fibers.contains(fiber));
        seen_fibers.insert(fiber);

        // Push it back into the queue; it should go to the end of the line
        ASSERT_EQ(0, monad_run_queue_try_push(rq, fiber));
    }
    // Everything was seen exactly once
    ASSERT_EQ(NumberOfFibers, seen_fibers.size());

    monad_run_queue_destroy(rq);
    for (auto *fiber : fibers) {
        monad_fiber_destroy(fiber);
    }
}

#endif
