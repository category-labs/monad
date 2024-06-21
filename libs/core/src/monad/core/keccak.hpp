#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/keccak.h>

#include <ethash/hash_types.hpp>

MONAD_NAMESPACE_BEGIN

using ::keccak256;

using hash256 = ethash::hash256;

inline hash256 keccak256(byte_string_view const bytes)
{
    hash256 hash;
    keccak256(bytes.data(), bytes.size(), hash.bytes);
    return hash;
}

template <size_t N>
inline hash256 keccak256(unsigned char const (&a)[N])
{
    return keccak256(to_byte_string_view(a));
}

MONAD_NAMESPACE_END
