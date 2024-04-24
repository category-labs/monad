#pragma once

#include <monad/config.hpp>

#include <evmc/evmc.hpp>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
#include <komihash.h>
#pragma GCC diagnostic pop

#include <cstddef>
#include <functional>

MONAD_NAMESPACE_BEGIN

using Address = ::evmc::address;

struct AddressHashCompare
{
    size_t hash(Address const &a) const
    {
        return komihash(a.bytes, 20, 0);
    }

    bool equal(Address const &a, Address const &b) const
    {
        return memcmp(a.bytes, b.bytes, 20) == 0;
    }
};

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
