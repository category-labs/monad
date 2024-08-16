#include <gtest/gtest.h>

#include "test_common.hpp"

#include "monad/async/work_dispatcher.h"

#include <chrono>
#include <thread>
#include <vector>

#include <pthread.h>

#ifndef __clang__
    #pragma GCC diagnostic ignored "-Wclass-memaccess"
#endif

TEST(work_dispatcher, DISABLED_works)
{
    struct thread_state
    {
        std::atomic<monad_async_work_dispatcher_executor> ex;
        std::thread thread;
        monad_async_executor_head stats{};

        thread_state() = default;

        thread_state(thread_state &&o) noexcept
            : thread(std::move(o.thread))
        {
        }

        ~thread_state()
        {
            if (thread.joinable()) {
                if (ex != nullptr) {
                    auto r = monad_async_make_success(-1);
                    to_result(monad_async_work_dispatcher_executor_wake(ex, &r))
                        .value();
                }
                thread.join();
            }
        }

        void launch(monad_async_work_dispatcher wd)
        {
            thread = std::thread(&thread_state::run, this, wd);
        }

        void run(monad_async_work_dispatcher wd)
        {
            struct monad_async_work_dispatcher_executor_attr ex_attr
            {
            };

            auto ex_ = make_work_dispatcher_executor(wd, ex_attr);
            ex.store(ex_.get());
            for (;;) {
                auto r = monad_async_work_dispatcher_executor_run(ex_.get());
                CHECK_RESULT(r);
                if (r.value < 0) {
                    break;
                }
            }
            memcpy(&stats, ex_->derived, sizeof(stats));
            ex.store(nullptr);
        }
    };

    struct monad_async_work_dispatcher_attr wd_attr
    {
    };

    auto wd = make_work_dispatcher(wd_attr);
    std::vector<thread_state> threads(std::thread::hardware_concurrency());

    for (auto &i : threads) {
        i.launch(wd.get());
    }

    struct task_state
    {
        task_ptr task;
        unsigned ops{0};

        task_state(monad_async_context_switcher switcher)
            : task([&] {
                monad_async_task_attr t_attr{};
                return make_task(switcher, t_attr);
            }())
        {
            task->user_code = task_state::run;
        }

        task_state(task_state &&o) noexcept
            : task(std::move(o.task))
            , ops(o.ops)
        {
        }

        void run()
        {
            ops++;
        }

        static monad_async_result run(monad_async_task task)
        {
            ((task_state *)task->user_ptr)->run();
            return monad_async_make_success(0);
        }
    };

    auto cs = make_context_switcher(monad_async_context_switcher_none);
    std::vector<task_state> tasks;
    for (size_t n = 0; n < 1024; n++) {
        tasks.emplace_back(cs.get());
    }
    for (auto &i : tasks) {
        i.task->user_ptr = &i;
    }

    std::vector<monad_async_task> task_ptrs;
    task_ptrs.resize(tasks.size());

    auto const begin = std::chrono::steady_clock::now();
    do {
        for (size_t n = 0; n < tasks.size(); n++) {
            if (monad_async_task_has_exited(tasks[n].task.get())) {
                task_ptrs[n] = tasks[n].task.get();
            }
            else {
                task_ptrs[n] = nullptr;
            }
        }
        CHECK_RESULT(monad_async_work_dispatcher_submit(
            wd.get(), task_ptrs.data(), task_ptrs.size()));
    }

    while (std::chrono::steady_clock::now() - begin < std::chrono::seconds(5));
    auto const end = std::chrono::steady_clock::now();
    CHECK_RESULT(monad_async_work_dispatcher_quit(wd.get(), 0, nullptr));
    for (auto &i : threads) {
        i.thread.join();
    }
    uint64_t ops = 0;
    for (auto &i : tasks) {
        ops += i.ops;
    }
    auto const diff =
        double(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin)
                   .count());
    std::cout << "   Dispatched " << ops << " pieces of work across "
              << threads.size() << " kernel threads which is "
              << (1000000000.0 * double(ops) / diff) << " ops/sec ("
              << (diff / double(ops)) << " ns/op)." << std::endl;
    std::cout << "\nIndividual executor CPU utilisation:";
    for (size_t n = 0; n < threads.size(); n++) {
        std::cout << "\n   " << n << ": "
                  << (100.0 -
                      (100.0 * double(threads[n].stats.total_ticks_sleeping) /
                       double(threads[n].stats.total_ticks_in_run)))
                  << "%";
    }
    std::cout << std::endl;
}
