#pragma once

#include <category/mpt/config.hpp>

#include <memory>
#include <stddef.h>

MONAD_MPT_NAMESPACE_BEGIN

struct Compute;

struct StateMachine
{
    virtual ~StateMachine() = default;
    virtual std::unique_ptr<StateMachine> clone() const = 0;
    virtual void down(unsigned char nibble) = 0;
    virtual void up(size_t) = 0;
    virtual Compute &get_compute() const = 0;
    virtual bool cache() const = 0;
    virtual bool compact() const = 0;

    virtual bool auto_expire() const
    {
        return false;
    }
};

MONAD_MPT_NAMESPACE_END
