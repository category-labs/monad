#pragma once

#include <monad/core/address.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

class HashFn
{
public:
    size_t operator()(Address const &k) const
    {
        return *reinterpret_cast<size_t const *>(k.hash.bytes);
    }
};

MONAD_NAMESPACE_END