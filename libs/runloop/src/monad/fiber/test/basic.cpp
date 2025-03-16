#include <atomic>
#include <bit>
#include <cerrno>
#include <cstddef>
#include <cstdint>

#include <gtest/gtest.h>

#include <monad/core/c_result.h>
#include <monad/fiber/fiber.h>

static monad_c_result yield_forever(monad_fiber_args_t mfa) noexcept
{
    auto *const pdone = std::bit_cast<std::atomic<bool> *>(mfa.arg[0]);
    std::intptr_t y = 0;
    while (!pdone->load(std::memory_order::relaxed)) {
        monad_fiber_yield(monad_c_make_success(y++));
    }
    return monad_c_make_success(y);
}

static monad_c_result no_nesting_func(monad_fiber_args_t /*unused*/) noexcept
{
    monad_fiber_t *nested_fiber;
    std::atomic<bool> done;

    monad_fiber_create(nullptr, &nested_fiber);
    monad_fiber_set_function(
        nested_fiber,
        MONAD_FIBER_PRIO_HIGHEST,
        yield_forever,
        {std::bit_cast<std::uintptr_t>(&done)});
    // Cannot run a nested fiber
    int const rc = monad_fiber_run(nested_fiber, nullptr);
    monad_fiber_destroy(nested_fiber);
    return rc == 0 ? monad_c_make_success(0) : monad_c_make_failure(rc);
}

TEST(fiber, basic)
{
    monad_fiber_t *fiber;
    monad_fiber_suspend_info_t suspend_info;
    std::atomic<bool> done;

    ASSERT_EQ(0, monad_fiber_create(nullptr, &fiber));

    // Nothing to run if we've never set a function
    ASSERT_EQ(ENXIO, monad_fiber_run(fiber, nullptr));

    ASSERT_EQ(
        0,
        monad_fiber_set_function(
            fiber,
            MONAD_FIBER_PRIO_HIGHEST,
            yield_forever,
            {std::bit_cast<std::uintptr_t>(&done)}));

    done.store(false);
    for (std::intptr_t expected = 0; expected < 10; ++expected) {
        ASSERT_EQ(0, monad_fiber_run(fiber, &suspend_info));
        ASSERT_EQ(MF_SUSPEND_YIELD, suspend_info.suspend_type);
        ASSERT_TRUE(MONAD_OK(suspend_info.eval));
        ASSERT_EQ(expected, suspend_info.eval.value);
    }

    done.store(true);
    ASSERT_EQ(0, monad_fiber_run(fiber, &suspend_info));
    ASSERT_EQ(MF_SUSPEND_RETURN, suspend_info.suspend_type);
    ASSERT_TRUE(MONAD_OK(suspend_info.eval));
    ASSERT_EQ(10, suspend_info.eval.value);
    ASSERT_EQ(ENXIO, monad_fiber_run(fiber, &suspend_info));

    // Reset the function; this resets the stack pointer to the beginning,
    // destroying the stack frame and thus the local state of the function;
    // the yield sequence will reset at 0.
    ASSERT_EQ(
        0,
        monad_fiber_set_function(
            fiber,
            MONAD_FIBER_PRIO_HIGHEST,
            yield_forever,
            {std::bit_cast<std::uintptr_t>(&done)}));

    done.store(false);
    for (std::uintptr_t expected = 0; expected < 10; ++expected) {
        ASSERT_EQ(0, monad_fiber_run(fiber, &suspend_info));
        ASSERT_EQ(MF_SUSPEND_YIELD, suspend_info.suspend_type);
        ASSERT_TRUE(MONAD_OK(suspend_info.eval));
        ASSERT_EQ(expected, suspend_info.eval.value);
    }

    // The function cannot be reset at any time, only before it has run or
    // after it has returned
    //   TODO(ken): when backporting this, explain why
    ASSERT_EQ(
        EBUSY,
        monad_fiber_set_function(
            fiber,
            MONAD_FIBER_PRIO_HIGHEST,
            yield_forever,
            {std::bit_cast<std::uintptr_t>(&done)}));

    monad_fiber_destroy(fiber);
}

TEST(fiber, no_fiber_nesting)
{
    monad_fiber_t *fiber;
    monad_fiber_suspend_info_t suspend_info;

    ASSERT_EQ(0, monad_fiber_create(nullptr, &fiber));
    ASSERT_EQ(
        0,
        monad_fiber_set_function(
            fiber, MONAD_FIBER_PRIO_HIGHEST, no_nesting_func, {}));

    ASSERT_EQ(0, monad_fiber_run(fiber, &suspend_info));
    ASSERT_EQ(MF_SUSPEND_RETURN, suspend_info.suspend_type);
    ASSERT_TRUE(MONAD_FAILED(suspend_info.eval));
    ASSERT_TRUE(
        outcome_status_code_equal_generic(&suspend_info.eval.error, ENOTSUP));

    monad_fiber_destroy(fiber);
}
