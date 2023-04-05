#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>

#include <variant>

MONAD_NAMESPACE_BEGIN

class IState
{
public:
    virtual ~IState() = default;
    virtual void commit() = 0;
};

MONAD_NAMESPACE_END