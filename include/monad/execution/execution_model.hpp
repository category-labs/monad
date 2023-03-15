#pragma once

#include <monad/execution/config.hpp>

#include <boost/fiber/all.hpp>

MONAD_EXECUTION_NAMESPACE_BEGIN

struct BoostFiberExecution
{
    using fiber_t = boost::fibers::fiber;
    static inline void yield() { boost::this_fiber::yield(); }
};

MONAD_EXECUTION_NAMESPACE_END
