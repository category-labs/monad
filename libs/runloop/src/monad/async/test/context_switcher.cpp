#include <gtest/gtest.h>

#include "test_common.hpp"

#include "monad/async/context_switcher.h"

#include "monad/async/task.h"

#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <sstream>
#include <stdexcept>
#include <utility>

/* Runtime pluggable context switchers:


   Testing none switcher ...
   Constructed and destroyed none switcher contexts at 4.26533e+07 ops/sec which
   is 23.4464 ns/op.


   Testing setjmp/longjmp switcher ...
   Constructed and destroyed setjmp/longjmp switcher contexts at 249754 ops/sec
   which is 4004.1 ns/op.


   Testing monad fiber switcher ...
   Constructed and destroyed monad fiber switcher contexts at 286373 ops/sec
   which is 3492.37 ns/op.


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
    auto cs_none = make_context_switcher(monad_async_context_switcher_none);
    auto cs_sjlj = make_context_switcher(monad_async_context_switcher_sjlj);
    auto cs_fcontext =
        make_context_switcher(monad_async_context_switcher_fcontext);

    auto test_creation_destruction = [](monad_async_context_switcher switcher,
                                        char const *desc) {
        {
            uint32_t ops = 0;
            monad_async_task_attr attr{.stack_size = 4096};
            std::cout << "\n\n   Testing " << desc << " ..." << std::endl;
            std::vector<context_ptr> contexts(10000);
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
    };
    // test_creation_destruction(cs_none.get(), "none switcher");
    // test_creation_destruction(cs_sjlj.get(), "setjmp/longjmp switcher");
    test_creation_destruction(cs_fcontext.get(), "fcontext switcher");
}

TEST(context_switcher, scaling)
{
#if MONAD_ASYNC_HAVE_ASAN || MONAD_ASYNC_HAVE_TSAN
    // The sanitisers try to map memory which fails causing the test to fail
    return;
#endif
#ifndef NDEBUG
    // All the internal debug checking code run takes too long if in debug mode
    return;
#endif
    auto test_scaling = [](monad_async_context_switcher switcher,
                           char const *desc) {
        {
            monad_async_task_attr attr{.stack_size = 512};
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
            make_context_switcher(monad_async_context_switcher_fcontext);
        test_scaling(cs_fcontext.get(), "fcontext switcher");
    }
    {
        auto cs_sjlj = make_context_switcher(monad_async_context_switcher_sjlj);
        test_scaling(cs_sjlj.get(), "setjmp/longjmp switcher");
    }
}
