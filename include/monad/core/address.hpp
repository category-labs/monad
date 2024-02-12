#pragma once

#include <monad/config.hpp>

#include <evmc/evmc.hpp>

#include <cstddef>
#include <functional>

MONAD_NAMESPACE_BEGIN

using Address = ::evmc::address;

static_assert(sizeof(Address) == 20);
static_assert(alignof(Address) == 1);

MONAD_NAMESPACE_END

namespace boost
{
    inline size_t hash_value(monad::Address const &address) noexcept
    {
        return std::hash<monad::Address>{}(address);
    }
}
