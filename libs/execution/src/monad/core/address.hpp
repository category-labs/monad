#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>

#include <evmc/evmc.hpp>

#include <cstddef>
#include <functional>

MONAD_NAMESPACE_BEGIN

using Address = ::evmc::address;

static_assert(sizeof(Address) == 20);
static_assert(alignof(Address) == 1);

Address address_from_secpkey(byte_string_fixed<65> const &);

MONAD_NAMESPACE_END

namespace boost
{
    inline size_t hash_value(monad::Address const &address) noexcept
    {
        return std::hash<monad::Address>{}(address);
    }
}
