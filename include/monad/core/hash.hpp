#pragma once

#include <ethash/keccak.hpp>

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>

MONAD_NAMESPACE_BEGIN

using hash256 = byte_string_fixed<sizeof(ethash::hash256)>;

// Wrapper function around ethash::keccak256 to return a friendlier type
inline hash256 keccak256(byte_string_view target)
{
    auto const hashed = ethash::keccak256(target.data(), target.size());
    return hash256(
            reinterpret_cast<hash256::value_type const*>(&hashed.str),
            sizeof(hashed));
}
 
MONAD_NAMESPACE_END
