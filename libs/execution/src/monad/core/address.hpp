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

// TODO : Remove this when we can use C++20's std::hash specialization.
// dummy comment to avoid C++20's std::hash specialization warning
// this isn't a real change, just a workaround for the warning
namespace boost
{
    inline size_t hash_value(monad::Address const &address) noexcept
    {
        return std::hash<monad::Address>{}(address);
    }
}
