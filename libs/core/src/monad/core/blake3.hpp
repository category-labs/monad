#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>

#include <blake3.h>
#include <ethash/hash_types.hpp>

MONAD_NAMESPACE_BEGIN

using hash256 = ethash::hash256;

inline hash256 blake3(byte_string_view const bytes)
{
    hash256 hash;
    static_assert(sizeof(hash256) == BLAKE3_OUT_LEN);

    blake3_hasher hasher;
    blake3_hasher_init(&hasher);
    blake3_hasher_update(&hasher, bytes.data(), bytes.size());
    blake3_hasher_finalize(&hasher, hash.bytes, BLAKE3_OUT_LEN);
    return hash;
}

MONAD_NAMESPACE_END
