#pragma once

#include <monad/core/cmemory.hpp>

#include <bit>

MONAD_NAMESPACE_BEGIN

template <class T>
constexpr T unaligned_load(unsigned char const *const buf)
{
    unsigned char data[sizeof(T)];
    cmemcpy(data, buf, sizeof(T));
    return std::bit_cast<T>(data);
}

MONAD_NAMESPACE_END
