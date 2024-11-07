#include <atomic>
#include <gtest/gtest.h>

#include "../../test_common.hpp"

#include "../context_switcher.h"

#include <monad/core/small_prng.hpp>

#include <chrono>

/* With GDB IPC

   Testing no switcher ...
   Switched 100000 no switcher contexts at 1.47059e+06 ops/sec which is 680.501
   ns/op.


   Testing setjmp/longjmp switcher ...
   Switched 100000 setjmp/longjmp switcher contexts at 1.44928e+06 ops/sec which
   is 699.775 ns/op.


   Testing fcontext switcher ...
   Switched 100000 fcontext switcher contexts at 1.44928e+06 ops/sec which is
   698.789 ns/op.
*/

/* Without GDB IPC

   Testing no switcher ...
   Switched 100000 no switcher contexts at 1.47059e+06 ops/sec which is 680.661
   ns/op.


   Testing setjmp/longjmp switcher ...
   Switched 100000 setjmp/longjmp switcher contexts at 1.44928e+06 ops/sec which
   is 694.875 ns/op.


   Testing fcontext switcher ...
   Switched 100000 fcontext switcher contexts at 1.44928e+06 ops/sec which is
   691.234 ns/op.
*/

TEST(context_switcher, more_realistic_benchmark)
{
    auto test = [](context_switcher_ptr switcher, char const *desc) {
        static constexpr size_t OPS = 100000;
        std::cout << "\n\n   Testing " << desc << " ..." << std::endl;
        struct shared_t
        {
            context_ptr context;
            size_t count{OPS};
            monad::small_prng rand;
            uint32_t volatile randout;
        } shared;
        struct monad_context_task_head task
        {
            .user_code = +[](monad_context_task task) -> monad_c_result {
                shared_t *shared = (shared_t *)task->user_ptr;
                monad_context context = shared->context.get();
                monad_context_switcher switcher =
                    (context != nullptr)
                        ? context->switcher.load(std::memory_order_acquire)
                        : nullptr;
                while (shared->count > 0) {
                    shared->count--;
                    // Do some work
                    for (size_t n = 0; n < 1024; n++) {
                        shared->randout = shared->rand();
                    }
                    if (switcher != nullptr) {
                        switcher->suspend_and_call_resume(context, nullptr);
                    }
                }
                return monad_c_make_success(0);
            },
            .user_ptr = (void *)&shared, .detach = +[](monad_context_task) {}
        };
        if (switcher) {
            monad_context_task_attr attr{
#if MONAD_HAVE_ASAN || MONAD_HAVE_TSAN
                .stack_size = 4096 * 4
#else
                .stack_size = 4096
#endif
            };
            shared.context = make_context(switcher.get(), &task, attr);
        }
        {
            auto const begin = std::chrono::steady_clock::now();
            while (std::chrono::steady_clock::now() - begin <
                   std::chrono::seconds(3))
                ;
        }
        auto const begin = std::chrono::steady_clock::now();
        if (switcher) {
            to_result(switcher->resume_many(
                          switcher.get(),
                          +[](void *user_ptr,
                              monad_context fake_context) -> monad_c_result {
                              shared_t *shared = (shared_t *)user_ptr;
                              while (shared->count > 0) {
                                  // May return, may reenter this function
                                  fake_context->switcher
                                      .load(std::memory_order_acquire)
                                      ->resume(
                                          fake_context, shared->context.get());
                              }
                              return monad_c_make_success(0);
                          },
                          (void *)&shared))
                .value();
        }
        else {
            to_result(task.user_code(&task)).value();
        }
        auto const end = std::chrono::steady_clock::now();
        std::cout
            << "   Switched " << OPS << " " << desc << " contexts at "
            << (1000.0 * double(OPS) /
                double(std::chrono::duration_cast<std::chrono::milliseconds>(
                           end - begin)
                           .count()))
            << " ops/sec which is "
            << (double(std::chrono::duration_cast<std::chrono::nanoseconds>(
                           end - begin)
                           .count()) /
                double(OPS))
            << " ns/op." << std::endl;
    };
    test({}, "no switcher");
    test(
        make_context_switcher(monad_context_switcher_sjlj),
        "setjmp/longjmp switcher");
    test(
        make_context_switcher(monad_context_switcher_fcontext),
        "fcontext switcher");
}
