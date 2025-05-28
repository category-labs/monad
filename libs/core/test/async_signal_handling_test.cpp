#include <monad/core/async_signal_handling.hpp>

#include <monad/config.hpp>
#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

#include <condition_variable>
#include <mutex>

#ifndef __clang__
    #if defined(__SANITIZE_THREAD__)
        #define HAVE_TSAN 1
    #endif
#else
    #if __has_feature(thread_sanitizer)
        #define HAVE_TSAN 1
    #endif
#endif

namespace
{
    TEST(AsyncSignalHandling, basic_signal_handling)
    {
#if HAVE_TSAN
        return; // TSAN complains about potential lock inversion in this test
#endif
        monad::async_signal_handling inst;
        std::mutex lock;
        std::condition_variable cond;
        int signal_handled = 0;
        auto h = monad::async_signal_handling::add_handler(
            SIGALRM,
            0,
            [&](const struct signalfd_siginfo &si,
                monad::async_signal_handling::handler *) -> bool {
                std::unique_lock g(lock);
                signal_handled++;
                std::cout << "Signal "
                          << monad::async_signal_handling::signal_description(
                                 (int)si.ssi_signo)
                          << " (" << si.ssi_signo << ") received!" << std::endl;
                cond.notify_one();
                return true;
            });
        std::unique_lock g(lock);
        alarm(1);
        cond.wait_for(g, std::chrono::seconds(3));
        h->mark_as_handled();
        EXPECT_EQ(signal_handled, 1);
        alarm(1);
        cond.wait_for(g, std::chrono::seconds(3));
        EXPECT_EQ(signal_handled, 2);
        h->mark_as_handled();
    }

    TEST(AsyncSignalHandling, timers)
    {
#if HAVE_TSAN
        return; // TSAN complains about potential lock inversion in this test
#endif
        monad::async_signal_handling inst;
        std::mutex lock;
        std::condition_variable cond;
        std::vector<monad::async_signal_handling::timer_ptr> timers;
        std::vector<int> fired;
        timers.reserve(15);
        fired.reserve(15);
        int idx = 0;
        for (uint64_t ns = 10000000000ULL; ns > 0; ns /= 10, idx++) {
            timers.emplace_back(monad::async_signal_handling::invoke_after(
                [&, idx]() -> void {
                    std::unique_lock g(lock);
                    fired.push_back(idx);
                    std::cout << "Timer " << idx << " fired!" << std::endl;
                    cond.notify_one();
                },
                ns));
        }
        // Deliberately leave the ten second wait dangle
        std::unique_lock g(lock);
        cond.wait_for(
            g, std::chrono::seconds(20), [&] { return fired.size() == 10; });
        EXPECT_EQ(fired.size(), 10);
        std::sort(fired.begin(), fired.end());
        for (size_t n = 0; n < fired.size(); n++) {
            EXPECT_EQ(fired[n], n + 1);
        }
    }

    struct timer_self_replace
    {
        std::mutex lock;
        std::condition_variable cond;
        monad::async_signal_handling::timer_ptr timer;
        size_t idx = 0;

        void operator()()
        {
            std::unique_lock g(lock);
            if (idx == 3) {
                cond.notify_one();
                return;
            }
            idx++;
            timer = monad::async_signal_handling::invoke_after(
                [this] { (*this)(); }, 1000000000ULL);
        }
    };

    TEST(AsyncSignalHandling, timer_self_replace)
    {
#if HAVE_TSAN
        return; // TSAN complains about potential lock inversion in this test
#endif
        monad::async_signal_handling inst;
        timer_self_replace impl;
        impl();
        std::unique_lock g(impl.lock);
        impl.cond.wait_for(g, std::chrono::seconds(5));
    }
}
