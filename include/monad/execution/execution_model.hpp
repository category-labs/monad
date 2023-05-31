#pragma once

#include <monad/execution/config.hpp>

#include <boost/fiber/all.hpp>

#include <thread>

MONAD_EXECUTION_NAMESPACE_BEGIN

struct BoostFiberExecution
{
    using fiber_t = boost::fibers::fiber;
    static void yield() noexcept { boost::this_fiber::yield(); }

    [[nodiscard]] constexpr static auto get_executor() noexcept
    {
        return [](auto &&f) {
            using result_t = decltype(std::declval<decltype(f)>()());
            boost::fibers::promise<result_t> promise;
            auto future = promise.get_future();
            std::jthread thread{[&promise, f] { promise.set_value(f()); }};
            return future.get();
        };
    }
};

MONAD_EXECUTION_NAMESPACE_END
