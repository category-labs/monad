#pragma once

#include <monad/config.hpp>

#include <boost/fiber/context.hpp>
#include <boost/fiber/properties.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

class fiber_properties final : public boost::fibers::fiber_properties
{
    uint64_t priority_ = 0;

public:
    explicit fiber_properties(boost::fibers::context *const ctx) noexcept
        : boost::fibers::fiber_properties{ctx}
    {
    }

    [[gnu::always_inline]] uint64_t getPriority() const noexcept
    {
        return priority_;
    }

    [[gnu::always_inline]] void setPriority(uint64_t const priority) noexcept
    {
        priority_ = priority;

        notify();
    }
};

MONAD_NAMESPACE_END
