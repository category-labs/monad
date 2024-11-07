#include <gtest/gtest.h>

#include "../../test_common.hpp"
#include "../config.h"
#include "monad/async/cpp_helpers.hpp"
#include "monad/async/task_impl.h"

#include "../context_switcher.h"

#include "monad/async/task.h"

#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <sstream>
#include <stdexcept>
#include <utility>

/* Runtime pluggable context switchers with GDB IPC enabled:

   Testing none switcher ...

   Constructed and destroyed none switcher contexts at 2.21733e+07 ops/sec which
is 45.1057 ns/op.


   Testing setjmp/longjmp switcher ...

   Constructed and destroyed setjmp/longjmp switcher contexts at 67157 ops/sec
which is 14892.6 ns/op.

   Switched 1000000 setjmp/longjmp switcher contexts at 1.75439e+07 ops/sec
which is 57.7857 ns/op.


   Testing fcontext switcher ...

   Constructed and destroyed fcontext switcher contexts at 69160.6 ops/sec which
is 14460.1 ns/op.

   Switched 1000000 fcontext switcher contexts at 2e+07 ops/sec which is 50.9227
ns/op.
*/

/* Runtime pluggable context switchers with GDB IPC disabled:

   Testing none switcher ...

   Constructed and destroyed none switcher contexts at 2.223e+07 ops/sec which
   is 44.9921 ns/op.


   Testing setjmp/longjmp switcher ...

   Constructed and destroyed setjmp/longjmp switcher contexts at 66371.7 ops/sec
   which is 15066.8 ns/op.

   Switched 1000000 setjmp/longjmp switcher contexts at 1.5625e+07 ops/sec which
   is 64.3646 ns/op.


   Testing fcontext switcher ...

   Constructed and destroyed fcontext switcher contexts at 69356.9 ops/sec which
   is 14419.5 ns/op.

   Switched 1000000 fcontext switcher contexts at 2.12766e+07 ops/sec which
   is 47.0094 ns/op.
*/

/*
Max creation limits before we run out of RAM:

    - none switcher was stopped after 2 billion instances, likely could go on
for much longer.

    - SJLJ and monad fiber switchers create about 32,743 instances before
ENOMEM. The cause is the Linux kernel per process VMA limit of 64k, each
stack and its guard page is a VMA region, so you get under half the 64k process
limit.
*/

TEST(context_switcher, works)
{
    auto cs_none = make_context_switcher(monad_context_switcher_none);
    auto cs_sjlj = make_context_switcher(monad_context_switcher_sjlj);
    auto cs_fcontext = make_context_switcher(monad_context_switcher_fcontext);

    auto test_creation_destruction = [](monad_context_switcher switcher,
                                        char const *desc,
                                        bool run_switching_test) {
        monad_context_task_attr attr{
#if MONAD_HAVE_ASAN || MONAD_HAVE_TSAN
            .stack_size = 4096 * 4
#else
            .stack_size = 4096
#endif
        };
        std::cout << "\n\n   Testing " << desc << " ..." << std::endl;
        std::vector<context_ptr> contexts(10000);
        {
            uint32_t ops = 0;
            auto const begin = std::chrono::steady_clock::now();
            do {
                for (auto &i : contexts) {
                    i = make_context(switcher, nullptr, attr);
                }
                ops += (uint32_t)contexts.size();
            }
            while (std::chrono::steady_clock::now() - begin <
                   std::chrono::seconds(3));
            for (auto &i : contexts) {
                i.reset();
            }
            auto const end = std::chrono::steady_clock::now();
            std::cout
                << "   Constructed and destroyed " << desc << " contexts at "
                << (1000.0 * double(ops) /
                    double(
                        std::chrono::duration_cast<std::chrono::milliseconds>(
                            end - begin)
                            .count()))
                << " ops/sec which is "
                << (double(std::chrono::duration_cast<std::chrono::nanoseconds>(
                               end - begin)
                               .count()) /
                    double(ops))
                << " ns/op." << std::endl;
        }
        if (run_switching_test) {
            struct shared_t
            {
                bool done{false};
                std::vector<std::pair<uint32_t, uint32_t>> counts;
                std::vector<context_ptr> *contexts;
                monad_context context;
                std::vector<context_ptr>::iterator it;
            } shared;
            struct monad_context_task_head task
            {
                .user_code = +[](monad_context_task task) -> monad_c_result {
                    shared_t *shared = (shared_t *)task->user_ptr;
                    monad_context context = shared->context;
                    monad_context_switcher switcher = context->switcher;
                    auto const myidx = shared->counts.size();
                    shared->counts.emplace_back(0, 0);
                    while (!shared->done) {
                        shared->counts[myidx].first++;
                        // Switch back to main
                        if (context != shared->context) {
                            abort();
                        }
                        switcher->suspend_and_call_resume(context, nullptr);
                        shared->counts[myidx].second++;
                    }
                    return monad_c_make_success(0);
                },
                .user_ptr = (void *)&shared,
                .detach = +[](monad_context_task) {}
            };
            // All contexts are constructed suspended in their base loop
            for (auto &i : contexts) {
                i = make_context(switcher, &task, attr);
            }
            shared.contexts = &contexts;
            auto const begin = std::chrono::steady_clock::now();
            for (size_t n = 0; n <= 100; n++) {
                shared.it = contexts.begin();
                if (n == 100) {
                    shared.done = true;
                }
                to_result(
                    switcher->resume_many(
                        switcher,
                        +[](void *user_ptr,
                            monad_context fake_context) -> monad_c_result {
                            shared_t *shared = (shared_t *)user_ptr;
                            for (;;) {
                                if (shared->it == shared->contexts->end()) {
                                    return monad_c_make_success(0);
                                }
                                shared->context = shared->it->get();
                                ++shared->it;
                                // May return, may reenter this function
                                fake_context->switcher
                                    .load(std::memory_order_acquire)
                                    ->resume(fake_context, shared->context);
                            }
                            return monad_c_make_success(0);
                        },
                        (void *)&shared))
                    .value();
            }
            auto const end = std::chrono::steady_clock::now();
            auto const ops = 100 * 10000;
            std::cout
                << "   Switched " << ops << " " << desc << " contexts at "
                << (1000.0 * double(ops) /
                    double(
                        std::chrono::duration_cast<std::chrono::milliseconds>(
                            end - begin)
                            .count()))
                << " ops/sec which is "
                << (double(std::chrono::duration_cast<std::chrono::nanoseconds>(
                               end - begin)
                               .count()) /
                    double(ops))
                << " ns/op." << std::endl;
            for (auto &i : shared.counts) {
                EXPECT_EQ(i.first, 100);
                EXPECT_EQ(i.second, 100);
            }
        }
    };
    test_creation_destruction(cs_none.get(), "none switcher", false);
    test_creation_destruction(cs_sjlj.get(), "setjmp/longjmp switcher", true);
    test_creation_destruction(cs_fcontext.get(), "fcontext switcher", true);
}

TEST(context_switcher, scaling)
{
#if MONAD_HAVE_ASAN || MONAD_HAVE_TSAN
    // The sanitisers try to map memory which fails causing the test to fail
    return;
#endif
#ifndef NDEBUG
    // All the internal debug checking code run takes too long if in debug mode
    return;
#endif
    auto test_scaling = [](monad_context_switcher switcher, char const *desc) {
        {
            monad_context_task_attr attr{.stack_size = 512};
            std::vector<context_ptr> contexts(16384);
            for (;;) {
                std::cout << "\n   Testing " << desc << " with "
                          << contexts.size() << " contexts ..." << std::endl;
                size_t items = 0;
                try {
                    for (auto &i : contexts) {
                        if (!i) {
                            i = make_context(switcher, nullptr, attr);
                        }
                        items++;
                    }
                }
                catch (std::exception const &e) {
                    std::cout << "\n      At item count " << items
                              << " failed to create context due to '"
                              << e.what() << "'." << std::endl;
#if 0
                    std::cout << "\n   Holding until Return is pressed so "
                                 "diagnostics can be run ..."
                              << std::endl;
                    getchar();
#endif
                    break;
                }
                contexts.resize(contexts.size() << 1);
            }
            for (auto &i : contexts) {
                i.reset();
            }
        }
    };
    // test_scaling(cs_none.get(), "none switcher");
    {
        auto cs_fcontext =
            make_context_switcher(monad_context_switcher_fcontext);
        test_scaling(cs_fcontext.get(), "fcontext switcher");
    }
    {
        auto cs_sjlj = make_context_switcher(monad_context_switcher_sjlj);
        test_scaling(cs_sjlj.get(), "setjmp/longjmp switcher");
    }
}

TEST(context_switcher, recursion)
{
    struct shared_t
    {
        context_switcher_ptr switcher;
        char const *desc;
        int level{0};
        bool done{false};
        monad_context current_context{nullptr};
    } shared;

    auto test_recursion = +[](monad_context_task task_) -> monad_c_result {
        auto *shared = (shared_t *)task_->user_ptr;
        for (int n = 0; n < shared->level; n++) {
            std::cout << " ";
        }
        std::cout << "   Testing " << shared->desc << " at "
                  << (shared->level + 1) << " deep ...";
        if (shared->level == 15) {
            std::cout << " done!" << std::endl;
            return monad_c_make_success(0);
        }
        std::cout << std::endl;
        shared->level++;
        struct monad_context_task_head task
        {
            .user_code = task_->user_code, .user_ptr = task_->user_ptr,
            .detach = +[](monad_context_task) {}
        };
        monad_context_task_attr attr{
#if MONAD_HAVE_ASAN || MONAD_HAVE_TSAN
            .stack_size = 4096 * 4
#else
            .stack_size = 4096
#endif
        };
        auto context = make_context(shared->switcher.get(), &task, attr);
        auto *old_context = shared->current_context;
        shared->current_context = context.get();
        shared->done = false;
        to_result(
            shared->switcher->resume_many(
                shared->switcher.get(),
                +[](void *user_ptr,
                    monad_context fake_context) -> monad_c_result {
                    shared_t *shared = (shared_t *)user_ptr;
                    if (!shared->done) {
                        shared->done = true;
                        fake_context->switcher.load(std::memory_order_acquire)
                            ->resume(fake_context, shared->current_context);
                    }
                    return monad_c_make_success(0);
                },
                (void *)shared))
            .value();
        shared->current_context = old_context;
        shared->level--;
        for (int n = 0; n < shared->level; n++) {
            std::cout << " ";
        }
        std::cout << "   Unwinding from " << (shared->level + 1) << " deep"
                  << std::endl;
        return monad_c_make_success(0);
    };
    {
        shared.switcher =
            make_context_switcher(monad_context_switcher_fcontext);
        shared.desc = "fcontext switcher";
        shared.level = 0;
        shared.current_context = nullptr;
        monad_context_task_head task{
            .user_code = test_recursion, .user_ptr = &shared};
        test_recursion(&task);
    }
    {
        shared.switcher = make_context_switcher(monad_context_switcher_sjlj);
        shared.desc = "setjmp/longjmp switcher";
        shared.level = 0;
        shared.current_context = nullptr;
        monad_context_task_head task{
            .user_code = test_recursion, .user_ptr = &shared};
        test_recursion(&task);
    }
}
