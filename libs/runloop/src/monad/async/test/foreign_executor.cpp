#include <atomic>
#include <gtest/gtest.h>

#include "../../test_common.hpp"

#include <monad/context/config.h>

#include "../executor.h"
#include "../task.h"

TEST(foreign_executor, works)
{
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 4;
    auto ex = make_executor(ex_attr);
    auto switcher = make_context_switcher(monad_context_switcher_sjlj);
    static auto print_stats = [](monad_async_task task, char const *desc) {
        std::cout << desc << ":\n   ticks_when_submitted = "
                  << task->ticks_when_submitted
                  << "\n   ticks_when_attached = " << task->ticks_when_attached
                  << "\n   ticks_when_detached = " << task->ticks_when_detached
                  << "\n   ticks_when_suspended_awaiting = "
                  << task->ticks_when_suspended_awaiting
                  << "\n   ticks_when_suspended_completed = "
                  << task->ticks_when_suspended_completed
                  << "\n   ticks_when_resumed = " << task->ticks_when_resumed
                  << "\n   total_ticks_executed = "
                  << task->total_ticks_executed << std::endl;
    };
    monad_async_task_attr t_attr{};
    auto task = make_task(switcher.get(), t_attr);

    struct shared_t
    {
        monad_context context;
        struct monad_async_task_head saved_async_task;
        int invokable_called{0}, resumed{0};
    } shared;

    shared.context = task->derived.context;
    task->derived.user_ptr = (void *)&shared;
    task->derived.user_code =
        +[](monad_context_task context_task) -> monad_c_result {
        monad_async_task task = (monad_async_task)context_task;
        auto *shared = (shared_t *)context_task->user_ptr;
        print_stats(task, "Just after first attach before 10 ms suspend");
        CHECK_RESULT(monad_async_task_suspend_for_duration(
            nullptr,
            ((monad_async_task)task),
            10000000ULL)); // 10 milliseconds
        print_stats(
            task, "After 10 ms suspend before suspend_save_detach_and_invoke");

        auto r = monad_async_task_suspend_save_detach_and_invoke(
            task,
            &shared->saved_async_task,
            +[](monad_context_task context_task) -> monad_c_result {
                auto *shared = (shared_t *)context_task->user_ptr;
                shared->invokable_called++;
                return monad_c_make_success(0);
            });
        CHECK_RESULT(r);
        if (r.value != 5) {
            abort();
        }
        print_stats(
            &shared->saved_async_task,
            "After suspend_save_detach_and_invoke in 'naked' context before "
            "raw suspend 1");
        context_task->context->switcher.load(std::memory_order_acquire)
            ->suspend_and_call_resume(context_task->context, nullptr);
        print_stats(task, "After raw suspend now back within the executor 1");

        r = monad_async_task_suspend_save_detach_and_invoke(
            task,
            nullptr,
            +[](monad_context_task context_task) -> monad_c_result {
                auto *shared = (shared_t *)context_task->user_ptr;
                shared->invokable_called++;
                return monad_c_make_success(0);
            });
        CHECK_RESULT(r);
        if (r.value != 6) {
            abort();
        }
        print_stats(
            task,
            "After suspend_save_detach_and_invoke in 'naked' context before "
            "raw suspend 2");
        context_task->context->switcher.load(std::memory_order_acquire)
            ->suspend_and_call_resume(context_task->context, nullptr);
        print_stats(task, "After raw suspend now back within the executor 2");
        return monad_c_make_success(0);
    };
    CHECK_RESULT(monad_async_task_attach(ex.get(), task.get(), nullptr));
    // This will exit when the task detaches itself
    while (monad_async_executor_has_work(ex.get())) {
        to_result(monad_async_executor_run(ex.get(), size_t(-1), nullptr))
            .value();
    }
    std::cout
        << "\nBack in main after executor has said there is no more work 1."
        << std::endl;
    // Manually resume the context to pretend we are a foreign executor
    memset(
        ((char *)task.get()) + sizeof(struct monad_context_task_head),
        0xff,
        sizeof(struct monad_async_task_head) -
            sizeof(struct monad_context_task_head));
    auto res = monad_c_make_success(5);
    memcpy((void *)&task->derived.result, &res, sizeof(monad_c_result));
    switcher->resume_many(
        switcher.get(),
        +[](void *user_ptr, monad_context fake_context) -> monad_c_result {
            auto *shared = (shared_t *)user_ptr;
            if (!shared->resumed) {
                shared->resumed = true;
                fake_context->switcher.load(std::memory_order_acquire)
                    ->resume(fake_context, shared->context);
            }
            return monad_c_make_success(0);
        },
        (void *)&shared);
    std::cout << "\nBack in main after raw context suspended itself as if in a "
                 "foreign executor 1"
              << std::endl;
    CHECK_RESULT(monad_async_task_attach(
        ex.get(),
        monad_async_task_from_foreign_context(
            &task->derived, &shared.saved_async_task),
        nullptr));
    while (monad_async_executor_has_work(ex.get())) {
        to_result(monad_async_executor_run(ex.get(), size_t(-1), nullptr))
            .value();
    }
    print_stats(task.get(), "\bBack in main 1");
    EXPECT_GT(
        task->total_ticks_executed,
        shared.saved_async_task.total_ticks_executed);

    shared.resumed = false;
    std::cout
        << "\nBack in main after executor has said there is no more work 2."
        << std::endl;
    // Manually resume the context to pretend we are a foreign executor
    memset(
        ((char *)task.get()) + sizeof(struct monad_context_task_head),
        0xff,
        sizeof(struct monad_async_task_head) -
            sizeof(struct monad_context_task_head));
    res = monad_c_make_success(6);
    memcpy((void *)&task->derived.result, &res, sizeof(monad_c_result));
    switcher->resume_many(
        switcher.get(),
        +[](void *user_ptr, monad_context fake_context) -> monad_c_result {
            auto *shared = (shared_t *)user_ptr;
            if (!shared->resumed) {
                shared->resumed = true;
                fake_context->switcher.load(std::memory_order_acquire)
                    ->resume(fake_context, shared->context);
            }
            return monad_c_make_success(0);
        },
        (void *)&shared);
    std::cout << "\nBack in main after raw context suspended itself as if in a "
                 "foreign executor 2"
              << std::endl;
    CHECK_RESULT(monad_async_task_attach(
        ex.get(),
        monad_async_task_from_foreign_context(&task->derived, nullptr),
        nullptr));
    while (monad_async_executor_has_work(ex.get())) {
        to_result(monad_async_executor_run(ex.get(), size_t(-1), nullptr))
            .value();
    }
    print_stats(task.get(), "\bBack in main wrapping up 2");
}
