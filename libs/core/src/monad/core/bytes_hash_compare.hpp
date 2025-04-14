#pragma once

#include <monad/config.hpp>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
#include <komihash.h>
#pragma GCC diagnostic pop

#include <type_traits>

MONAD_NAMESPACE_BEGIN

template <class Bytes>
    requires std::is_trivially_copyable_v<Bytes>
struct BytesHashCompare
{
    size_t hash(Bytes const &a) const
    {
        return komihash(&a, sizeof(Bytes), 0);
    }

    bool equal(Bytes const &a, Bytes const &b) const
    {
        return memcmp(&a, &b, sizeof(Bytes)) == 0;
    }

    bool operator()(Bytes const &a) const
    {
        return hash(a);
    }
};

MONAD_NAMESPACE_END
