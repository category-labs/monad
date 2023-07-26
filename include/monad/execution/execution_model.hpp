#pragma once

#include <monad/execution/config.hpp>

#include <boost/fiber/all.hpp>

#include <concepts>
#include <thread>

MONAD_EXECUTION_NAMESPACE_BEGIN

struct BoostFiberExecution
{
    using fiber_t = boost::fibers::fiber;
    static void yield() noexcept { boost::this_fiber::yield(); }

    [[nodiscard]] static auto execute(std::invocable auto &&f)
    {
        using result_t = decltype(std::declval<decltype(f)>()());
        boost::fibers::promise<result_t> promise;
        auto future = promise.get_future();
        std::jthread thread{[&promise, &f] {
            promise.set_value(std::invoke(std::forward<decltype(f)>(f)));
        }};
        return future.get();
    }
};

struct SerialExecution
{
    [[nodiscard]] constexpr static auto execute(std::invocable auto &&f)
    {
        return std::invoke(std::forward<decltype(f)>(f));
    }
};

MONAD_EXECUTION_NAMESPACE_END
