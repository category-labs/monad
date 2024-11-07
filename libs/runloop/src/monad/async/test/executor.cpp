#include <gtest/gtest.h>

#include "../../test_common.hpp"

#include <monad/context/config.h>

#include "../executor.h"
#include "../task.h"

#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <thread>

/* Post runtime pluggable context switchers:

   Task attach to task initiate took 360 ticks.
   Task initiate to task detach took 360 ticks.
   Task executed for a total of 360 ticks.

   Task attach to task initiate took 468 ticks.
   Task initiate to task suspend await took 432 ticks.
   Task suspend await to task suspend completed took 17352 ticks.
   Task suspend completed to task resume took 180 ticks.
   Task resume to task detach took 432 ticks.
   Task executed for a total of 864 ticks.


   Initiated, executed and tore down 2.52525e+07 ops/sec which is 39.6002 ns/op.


   Suspend-resume 1.16596e+07 ops/sec which is 85.7663 ns/op.
*/

TEST(async_result, works)
{
    auto r = monad_c_make_success(EINVAL);
    CHECK_RESULT(r);
    try {
        r = monad_c_make_failure(EINVAL);
        CHECK_RESULT(r);
    }
    catch (std::exception const &e) {
        EXPECT_STREQ(e.what(), "Invalid argument");
    }
    auto r2(to_result(r));
    try {
        r2.value();
    }
    catch (std::exception const &e) {
        EXPECT_STREQ(e.what(), "Invalid argument");
    }
}

TEST(executor, works)
{
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 64;
    auto ex = make_executor(ex_attr);

    struct timespec ts
    {
        0, 0
    };

    auto r = monad_async_executor_run(ex.get(), 1, &ts);
    try {
        CHECK_RESULT(r);
    }
    catch (std::exception const &e) {
        EXPECT_STREQ(e.what(), "Timer expired");
    }
    {
        auto begin = std::chrono::steady_clock::now();
        while (std::chrono::steady_clock::now() - begin <
               std::chrono::seconds(1)) {
        }
    }
    monad_async_task_attr t_attr{};
    std::cout << "\n\n   With none context switcher ..." << std::endl;
    for (size_t n = 0; n < 10; n++) {
        auto s1 = make_context_switcher(monad_context_switcher_none);
        auto t1 = make_task(s1.get(), t_attr);
        bool did_run = false;
        t1->derived.user_ptr = (void *)&did_run;
        t1->derived.user_code = +[](monad_context_task task) -> monad_c_result {
            *(bool *)task->user_ptr = true;
            auto *current_executor =
                ((monad_async_task)task)
                    ->current_executor.load(std::memory_order_acquire);
            if (current_executor == nullptr) {
                abort();
            }
            EXPECT_EQ(current_executor->current_task, ((monad_async_task)task));
            EXPECT_EQ(current_executor->tasks_pending_launch, 0);
            EXPECT_EQ(current_executor->tasks_running, 1);
            EXPECT_EQ(current_executor->tasks_suspended, 0);
            return monad_c_make_success(5);
        };
        r = monad_async_task_attach(ex.get(), t1.get(), nullptr);
        CHECK_RESULT(r);
        EXPECT_TRUE(t1->is_pending_launch);
        EXPECT_FALSE(t1->is_running);
        EXPECT_FALSE(t1->is_suspended_awaiting);
        EXPECT_FALSE(t1->is_suspended_completed);
        EXPECT_EQ(ex->current_task, nullptr);
        EXPECT_EQ(ex->tasks_pending_launch, 1);
        EXPECT_EQ(ex->tasks_running, 0);
        EXPECT_EQ(ex->tasks_suspended, 0);
        r = monad_async_executor_run(ex.get(), 1, &ts);
        EXPECT_EQ(ex->tasks_pending_launch, 0);
        EXPECT_EQ(ex->tasks_running, 0);
        EXPECT_EQ(ex->tasks_suspended, 0);
        CHECK_RESULT(r);
        EXPECT_EQ(r.value, 1);
        EXPECT_FALSE(t1->is_pending_launch);
        EXPECT_FALSE(t1->is_running);
        EXPECT_FALSE(t1->is_suspended_awaiting);
        EXPECT_FALSE(t1->is_suspended_completed);
        CHECK_RESULT(t1->derived.result);
        EXPECT_EQ(t1->derived.result.value, 5);
        EXPECT_TRUE(did_run);
        if (n == 9) {
            std::cout << "\n   Task attach to task initiate took "
                      << (t1->ticks_when_resumed - t1->ticks_when_attached)
                      << " ticks.";
            std::cout << "\n   Task initiate to task detach took "
                      << (t1->ticks_when_detached - t1->ticks_when_resumed)
                      << " ticks.";
            std::cout << "\n   Task executed for a total of "
                      << t1->total_ticks_executed << " ticks." << std::endl;
        }
    }
    {
        auto test = [&ex](monad_context_switcher switcher, char const *desc) {
            static size_t n;
            monad_async_task_attr t_attr{};
            struct timespec ts
            {
                0, 0
            };
            std::cout << "\n\n   With " << desc << " context switcher ..."
                      << std::endl;
            for (n = 0; n < 10; n++) {
                auto t1 = make_task(switcher, t_attr);
                int did_run = 0;
                t1->derived.user_ptr = (void *)&did_run;
                t1->derived.user_code =
                    +[](monad_context_task task) -> monad_c_result {
                    *(int *)task->user_ptr = 1;
                    auto *current_executor =
                        ((monad_async_task)task)
                            ->current_executor.load(std::memory_order_acquire);
                    EXPECT_EQ(
                        current_executor->current_task,
                        ((monad_async_task)task));
                    EXPECT_EQ(current_executor->tasks_pending_launch, 0);
                    EXPECT_EQ(current_executor->tasks_running, 1);
                    EXPECT_EQ(current_executor->tasks_suspended, 0);
                    CHECK_RESULT(monad_async_task_suspend_for_duration(
                        nullptr,
                        ((monad_async_task)task),
                        10000000ULL)); // 10 milliseconds
                    *(int *)task->user_ptr = 2;
                    current_executor =
                        ((monad_async_task)task)
                            ->current_executor.load(std::memory_order_acquire);
                    EXPECT_EQ(
                        current_executor->current_task,
                        ((monad_async_task)task));
                    EXPECT_EQ(current_executor->tasks_pending_launch, 0);
                    EXPECT_EQ(current_executor->tasks_running, 1);
                    EXPECT_EQ(current_executor->tasks_suspended, 0);
                    return monad_c_make_success(5);
                };
                auto const suspend_begins = std::chrono::steady_clock::now();
                auto r = monad_async_task_attach(ex.get(), t1.get(), nullptr);
                CHECK_RESULT(r);
                EXPECT_TRUE(t1->is_pending_launch);
                EXPECT_FALSE(t1->is_running);
                EXPECT_FALSE(t1->is_suspended_awaiting);
                EXPECT_FALSE(t1->is_suspended_completed);
                EXPECT_EQ(ex->current_task, nullptr);
                EXPECT_EQ(ex->tasks_pending_launch, 1);
                EXPECT_EQ(ex->tasks_running, 0);
                EXPECT_EQ(ex->tasks_suspended, 0);
                ts.tv_sec = 3; // timeout and fail the test after this
                r = monad_async_executor_run(
                    ex.get(), 1, &ts); // runs and suspends
                monad_cpu_ticks_count_t const ticks_when_resumed =
                    t1->ticks_when_resumed;
                EXPECT_EQ(did_run, 1);
                EXPECT_EQ(ex->tasks_pending_launch, 0);
                EXPECT_EQ(ex->tasks_running, 0);
                EXPECT_EQ(ex->tasks_suspended, 1);
                CHECK_RESULT(r);
                EXPECT_EQ(r.value, 1);
                EXPECT_FALSE(t1->is_pending_launch);
                EXPECT_FALSE(t1->is_running);
                EXPECT_TRUE(t1->is_suspended_awaiting);
                EXPECT_FALSE(t1->is_suspended_completed);
                r = monad_async_executor_run(
                    ex.get(), 1, &ts); // resumes and exits
                EXPECT_EQ(did_run, 2);
                EXPECT_EQ(ex->tasks_pending_launch, 0);
                EXPECT_EQ(ex->tasks_running, 0);
                EXPECT_EQ(ex->tasks_suspended, 0);
                CHECK_RESULT(r);
                EXPECT_EQ(r.value, 1);
                EXPECT_FALSE(t1->is_pending_launch);
                EXPECT_FALSE(t1->is_running);
                EXPECT_FALSE(t1->is_suspended_awaiting);
                EXPECT_FALSE(t1->is_suspended_completed);
                CHECK_RESULT(t1->derived.result);
                EXPECT_EQ(t1->derived.result.value, 5);
                if (auto diff =
                        std::chrono::steady_clock::now() - suspend_begins;
                    diff < std::chrono::milliseconds(10)) {
                    std::cout << "   NOTE: On iteration " << n << ": "
                              << std::chrono::duration_cast<
                                     std::chrono::milliseconds>(diff)
                                     .count()
                              << " milliseconds have elapsed since suspend "
                                 "initiation. If it went to completed in "
                                 "less than 10 milliseconds, there is "
                                 "something wrong with the implementation."
                              << std::endl;
                    EXPECT_GE(diff, std::chrono::milliseconds(10));
                }
                if (n == 9) {
                    std::cout << "\n   Task attach to task initiate took "
                              << (ticks_when_resumed - t1->ticks_when_attached)
                              << " ticks.";
                    std::cout
                        << "\n   Task initiate to task suspend await took "
                        << (t1->ticks_when_suspended_awaiting -
                            ticks_when_resumed)
                        << " ticks.";
                    std::cout << "\n   Task suspend await to task suspend "
                                 "completed took "
                              << (t1->ticks_when_suspended_completed -
                                  t1->ticks_when_suspended_awaiting)
                              << " ticks.";
                    std::cout
                        << "\n   Task suspend completed to task resume took "
                        << (t1->ticks_when_resumed -
                            t1->ticks_when_suspended_completed)
                        << " ticks.";
                    std::cout
                        << "\n   Task resume to task detach took "
                        << (t1->ticks_when_detached - t1->ticks_when_resumed)
                        << " ticks.";
                    std::cout << "\n   Task executed for a total of "
                              << t1->total_ticks_executed << " ticks."
                              << std::endl;
                }
            }
            EXPECT_EQ(ex->total_io_submitted, ex->total_io_completed);
        };
        test(
            make_context_switcher(monad_context_switcher_fcontext).get(),
            "fcontext");
        test(
            make_context_switcher(monad_context_switcher_sjlj).get(),
            "setjmp/longjmp");
    }

    {
        auto cs = make_context_switcher(monad_context_switcher_none);

        struct shared_t
        {
            uint64_t ops{0};
        } shared;

        auto func = +[](monad_context_task task) -> monad_c_result {
            auto *shared = (shared_t *)task->user_ptr;
            shared->ops++;
            return monad_c_make_success(0);
        };
        std::vector<task_ptr> tasks;
        tasks.reserve(1024);
        for (size_t n = 0; n < 1024; n++) {
            tasks.push_back(make_task(cs.get(), t_attr));
            tasks.back()->derived.user_code = func;
            tasks.back()->derived.user_ptr = (void *)&shared;
        }
        std::cout << "\n\n   With none context switcher ..." << std::endl;
        auto const begin = std::chrono::steady_clock::now();
        do {
            for (auto &i : tasks) {
                auto r = monad_async_task_attach(ex.get(), i.get(), nullptr);
                CHECK_RESULT(r);
            }
            auto r = monad_async_executor_run(ex.get(), size_t(-1), nullptr);
            CHECK_RESULT(r);
            if (r.value != 1024) {
                abort();
            }
        }
        while (std::chrono::steady_clock::now() - begin <
               std::chrono::seconds(3));
        while (ex->tasks_running > 0 || ex->tasks_suspended > 0) {
            auto r = monad_async_executor_run(ex.get(), size_t(-1), nullptr);
            CHECK_RESULT(r);
        }
        auto const end = std::chrono::steady_clock::now();
        std::cout
            << "   Initiated, executed and tore down "
            << (1000.0 * double(shared.ops) /
                double(std::chrono::duration_cast<std::chrono::milliseconds>(
                           end - begin)
                           .count()))
            << " ops/sec which is "
            << (double(std::chrono::duration_cast<std::chrono::nanoseconds>(
                           end - begin)
                           .count()) /
                double(shared.ops))
            << " ns/op." << std::endl;
        EXPECT_EQ(ex->total_io_submitted, ex->total_io_completed);
    }

    {
        auto test = [&ex](monad_context_switcher switcher, char const *desc) {
            monad_async_task_attr t_attr{};
            struct shared_t
            {
                uint64_t ops{0};
                bool done{false};
            } shared;

            auto func = +[](monad_context_task task) -> monad_c_result {
                auto *shared = (shared_t *)task->user_ptr;
                while (!shared->done) {
                    shared->ops++;
                    auto r = monad_async_task_suspend_for_duration(
                        nullptr, ((monad_async_task)task), 0);
                    CHECK_RESULT(r);
                }
                return monad_c_make_success(0);
            };
            std::vector<task_ptr> tasks;
            tasks.reserve(64);
            for (size_t n = 0; n < 64; n++) {
                tasks.push_back(make_task(switcher, t_attr));
                tasks.back()->derived.user_code = func;
                tasks.back()->derived.user_ptr = (void *)&shared;
                auto r = monad_async_task_attach(
                    ex.get(), tasks.back().get(), nullptr);
                CHECK_RESULT(r);
            }
            std::cout << "\n\n   With " << desc << " context switcher ..."
                      << std::endl;
            auto const begin = std::chrono::steady_clock::now();
            do {
                auto r =
                    monad_async_executor_run(ex.get(), size_t(-1), nullptr);
                CHECK_RESULT(r);
            }
            while (std::chrono::steady_clock::now() - begin <
                   std::chrono::seconds(3));
            auto const end = std::chrono::steady_clock::now();
            shared.done = true;
            while (ex->tasks_running > 0 || ex->tasks_suspended > 0) {
                auto r =
                    monad_async_executor_run(ex.get(), size_t(-1), nullptr);
                CHECK_RESULT(r);
            }
            EXPECT_EQ(ex->total_io_submitted, ex->total_io_completed);
            std::cout
                << "   Suspend-resume "
                << (1000.0 * double(shared.ops) /
                    double(
                        std::chrono::duration_cast<std::chrono::milliseconds>(
                            end - begin)
                            .count()))
                << " ops/sec which is "
                << (double(std::chrono::duration_cast<std::chrono::nanoseconds>(
                               end - begin)
                               .count()) /
                    double(shared.ops))
                << " ns/op." << std::endl;
        };
        test(
            make_context_switcher(monad_context_switcher_fcontext).get(),
            "fcontext");
        test(
            make_context_switcher(monad_context_switcher_sjlj).get(),
            "setjmp/longjmp");
    }
}

TEST(executor, foreign_thread)
{
    auto test = [](monad_context_switcher_impl switcher_impl,
                   char const *desc) {
        std::cout << "\n   With " << desc << " context switcher ..."
                  << std::endl;
        struct executor_thread
        {
            executor_ptr executor;
            context_switcher_ptr switcher;
            std::thread thread;
            uint32_t ops{0};
        };

        std::vector<executor_thread> executor_threads{
            std::thread::hardware_concurrency()};
        std::atomic<int> latch{0};
        for (size_t n = 0; n < executor_threads.size(); n++) {
            executor_threads[n].thread = std::thread(
                [&latch, &switcher_impl](executor_thread *state) {
                    monad_async_executor_attr ex_attr{};
                    state->executor = make_executor(ex_attr);
                    state->switcher = make_context_switcher(switcher_impl);
                    latch++;
                    for (;;) {
                        auto r = to_result(monad_async_executor_run(
                            state->executor.get(), size_t(-1), nullptr));
                        if (!r) {
                            if (r.assume_error() == errc::operation_canceled) {
                                break;
                            }
                            std::cerr << "FATAL: "
                                      << r.assume_error().message().c_str()
                                      << std::endl;
                            abort();
                        }
                        state->ops += uint32_t(r.assume_value());
                    }
                    assert(
                        state->executor->total_io_submitted ==
                        state->executor->total_io_completed);
                    state->executor.reset();
                },
                &executor_threads[n]);
        }

        static bool checking = false;

        struct task
        {
            task_ptr task;
            uint32_t ops{0};

            static monad_c_result run(monad_context_task t_)
            {
                auto *t = ((monad_async_task)t_);
                auto *self = (struct task *)t_->user_ptr;
                self->ops++;
                if (checking) {
                    EXPECT_EQ(self->ops, 1);
                    EXPECT_EQ(
                        t->current_executor.load(std::memory_order_acquire)
                            ->current_task,
                        t);
                    EXPECT_FALSE(t->is_awaiting_dispatch);
                    EXPECT_FALSE(t->is_pending_launch);
                    EXPECT_TRUE(t->is_running);
                    EXPECT_FALSE(t->is_suspended_awaiting);
                    EXPECT_FALSE(t->is_suspended_completed);
                }
                return monad_c_make_success(0);
            }
        };

        std::vector<task> tasks(1024);
        monad_async_task_attr attr{};
        auto switcher = make_context_switcher(switcher_impl);
        for (auto &i : tasks) {
            i.task = make_task(switcher.get(), attr);
            i.task->derived.user_code = task::run;
            i.task->derived.user_ptr = (void *)&i;
        }
        while (latch < (int)executor_threads.size()) {
            std::this_thread::yield();
        }
        std::cout << "   All " << executor_threads.size()
                  << " executor threads have launched!" << std::endl;

        {
            auto *task = tasks.front().task.get();
            auto *ex = executor_threads.front().executor.get();
            auto *switcher = executor_threads.front().switcher.get();
            EXPECT_EQ(tasks.front().ops, 0);
            EXPECT_EQ(task->current_executor, nullptr);
            EXPECT_FALSE(task->is_awaiting_dispatch);
            EXPECT_FALSE(task->is_pending_launch);
            EXPECT_FALSE(task->is_running);
            EXPECT_FALSE(task->is_suspended_awaiting);
            EXPECT_FALSE(task->is_suspended_completed);
            CHECK_RESULT(monad_async_task_attach(ex, task, switcher));
            std::cout << "   First task attached, waiting for an executor "
                         "thread to launch it ..."
                      << std::endl;
            while (!monad_async_task_has_exited(task)) {
                std::this_thread::yield();
            }
            EXPECT_EQ(ex->tasks_pending_launch, 0);
            EXPECT_EQ(ex->tasks_running, 0);
            EXPECT_FALSE(task->is_awaiting_dispatch);
            EXPECT_FALSE(task->is_pending_launch);
            EXPECT_FALSE(task->is_running);
            EXPECT_FALSE(task->is_suspended_awaiting);
            EXPECT_FALSE(task->is_suspended_completed);
            EXPECT_EQ(tasks.front().ops, 1);
            std::cout << "   First task has executed." << std::endl;
        }
        checking = false;

        auto const begin = std::chrono::steady_clock::now();
        size_t n = 0;
        do {
            for (auto &i : tasks) {
                if (monad_async_task_has_exited(i.task.get())) {
                    auto &threadstate = executor_threads[n++];
                    CHECK_RESULT(monad_async_task_attach(
                        threadstate.executor.get(),
                        i.task.get(),
                        threadstate.switcher.get()));
                    if (n >= executor_threads.size()) {
                        n = 0;
                    }
                }
            }
        }
        while (std::chrono::steady_clock::now() - begin <
               std::chrono::seconds(5));
        std::cout
            << "   Five seconds has passed, cancelling executor threads ..."
            << std::endl;
        auto cancelled = monad_c_make_failure(ECANCELED);
        for (auto &i : executor_threads) {
            CHECK_RESULT(
                monad_async_executor_wake(i.executor.get(), &cancelled));
        }
        for (auto &i : executor_threads) {
            i.thread.join();
        }
        auto const end = std::chrono::steady_clock::now();
        auto const diff = double(
            std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin)
                .count());
        uint64_t executor_ops = 0;
        for (auto &i : executor_threads) {
            executor_ops += i.ops;
        }
        uint64_t task_ops = 0;
        for (auto &i : tasks) {
            task_ops += i.ops;
        }
        EXPECT_GE(task_ops, executor_ops);
        std::cout << "   Executed " << task_ops << " tasks on "
                  << executor_threads.size() << " kernel threads at "
                  << (1000000000.0 * double(task_ops) / diff) << " ops/sec ("
                  << (diff / double(task_ops)) << " ns/op)" << std::endl;
        tasks.clear();
    };
    test(monad_context_switcher_none, "none");
    test(monad_context_switcher_fcontext, "fcontext");
    test(monad_context_switcher_sjlj, "setjmp/longjmp");
}

TEST(executor, registered_io_buffers)
{
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 1;
    ex_attr.io_uring_wr_ring.entries = 1;
    ex_attr.io_uring_wr_ring.registered_buffers.small_count = 1;
    auto ex = make_executor(ex_attr);
    auto switcher = make_context_switcher(monad_context_switcher_sjlj);

    struct shared_t
    {
        std::set<monad_async_task> have_buffer, waiting_for_buffer;
    } shared;

    auto task_impl = +[](monad_context_task task_) -> monad_c_result {
        auto *shared = (shared_t *)task_->user_ptr;
        auto *task = ((monad_async_task)task_);
        shared->waiting_for_buffer.insert(task);
        monad_async_task_registered_io_buffer buffer{};
        to_result(monad_async_task_claim_registered_file_io_write_buffer(
                      &buffer, task, 1, {}))
            .value();
        shared->waiting_for_buffer.erase(task);
        shared->have_buffer.insert(task);
        to_result(monad_async_task_suspend_for_duration(nullptr, task, 0))
            .value();
        to_result(
            monad_async_task_release_registered_io_buffer(task, buffer.index))
            .value();
        shared->have_buffer.erase(task);
        return monad_c_make_success(0);
    };

    monad_async_task_attr t_attr{};
    std::vector<task_ptr> tasks;
    for (size_t n = 0; n < 10; n++) {
        tasks.push_back(make_task(switcher.get(), t_attr));
        tasks.back()->derived.user_code = task_impl;
        tasks.back()->derived.user_ptr = (void *)&shared;
        to_result(
            monad_async_task_attach(ex.get(), tasks.back().get(), nullptr))
            .value();
    }
    to_result(monad_async_executor_run(ex.get(), 10, nullptr)).value();
    bool have_buffer = true;
    do {
        to_result(monad_async_executor_run(ex.get(), 1, nullptr)).value();
        std::cout << "have_buffer=" << shared.have_buffer.size()
                  << " waiting_for_buffer=" << shared.waiting_for_buffer.size()
                  << std::endl;
        // One executor pump should resume the task holding the buffer which
        // releases it Next executor pump should resume the next task awaiting
        // the buffer
        have_buffer = !have_buffer;
        EXPECT_EQ(have_buffer, shared.have_buffer.size());
    }
    while (shared.have_buffer.size() + shared.waiting_for_buffer.size() > 0);
}
