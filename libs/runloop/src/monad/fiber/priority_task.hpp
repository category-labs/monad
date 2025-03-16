#pragma once

#include <monad/fiber/config.hpp>

#include <cstdint>
#include <functional>

MONAD_FIBER_NAMESPACE_BEGIN

struct PriorityTask
{
    int64_t priority{0};
    std::function<void()> task;
};

static_assert(sizeof(PriorityTask) == 40);
static_assert(alignof(PriorityTask) == 8);

MONAD_FIBER_NAMESPACE_END
