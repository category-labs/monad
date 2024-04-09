#pragma once

#include <monad/fiber2/config.hpp>

#include <boost/context/fiber.hpp>

MONAD_FIBER_NAMESPACE_BEGIN

inline thread_local boost::context::fiber dispatcher_{};

void yield()
{
    dispatcher_ = std::move(dispatcher_).resume();
}

MONAD_FIBER_NAMESPACE_END
