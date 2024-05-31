#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/keccak.h>

#include <ethash/hash_types.hpp>

MONAD_NAMESPACE_BEGIN

using hash256 = ethash::hash256;

inline hash256 keccak256(unsigned char const *const in, unsigned long const len)
{
    hash256 hash;
    ::keccak256(in, len, hash.bytes);
    return hash;
}

inline hash256 keccak256(byte_string_view const bytes)
{
    return keccak256(bytes.data(), bytes.size());
}

MONAD_NAMESPACE_END
