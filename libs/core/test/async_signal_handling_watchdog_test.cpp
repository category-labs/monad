
#include <monad/core/async_signal_handling.hpp>

#include <gtest/gtest.h>

// DO NOT include gtest_signal_stacktrace_printer.hpp here, it interferes with
// Google Test's death test handling

#include <thread>

namespace
{
    TEST(AsyncSignalHandling, unhandled_signal_causes_death)
    {
        testing::FLAGS_gtest_death_test_style = "threadsafe";

        monad::async_signal_handling inst;
        std::cout
            << "   Global async signal handler installed, raising SIGPOLL ... "
            << std::endl;
        kill(getpid(), SIGPOLL);
        std::cout << "   SIGPOLL has been raised!" << std::endl;
        std::this_thread::sleep_for(std::chrono::seconds(30));
        std::cout << "   Thread sleep exits" << std::endl;
        EXPECT_FALSE(true);
    }

}
