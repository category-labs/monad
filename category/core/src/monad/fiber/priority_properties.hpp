#pragma once

#include <monad/fiber/config.hpp>

#include <boost/fiber/context.hpp>
#include <boost/fiber/properties.hpp>

#include <cstdint>

MONAD_FIBER_NAMESPACE_BEGIN

using boost::fibers::context;
using boost::fibers::fiber_properties;

class PriorityProperties final : public fiber_properties
{
    uint64_t priority_ = 0;

public:
    explicit PriorityProperties(context *const ctx) noexcept
        : fiber_properties{ctx}
    {
    }

    [[gnu::always_inline]] uint64_t get_priority() const noexcept
    {
        return priority_;
    }

    [[gnu::always_inline]] void set_priority(uint64_t const priority) noexcept
    {
        priority_ = priority;

        notify();
    }
};

MONAD_FIBER_NAMESPACE_END
