#pragma once

#include <monad/config.hpp>

#include <monad/core/int.hpp>

#include <evmc/evmc.hpp>


#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
#include <komihash.h>
#pragma GCC diagnostic pop

#include <bit>
#include <cstddef>
#include <functional>

MONAD_NAMESPACE_BEGIN

using bytes32_t = ::evmc::bytes32;

static_assert(sizeof(bytes32_t) == 32);
static_assert(alignof(bytes32_t) == 1);

struct Bytes32HashCompare
{
    size_t hash(bytes32_t const &a) const
    {
        return komihash(a.bytes, 32, 0);
    }

    bool equal(bytes32_t const &a, bytes32_t const &b) const
    {
        return memcmp(a.bytes, b.bytes, 32) == 0;
    }
};

constexpr bytes32_t to_bytes(uint256_t const n) noexcept
{
    return std::bit_cast<bytes32_t>(n);
}

using namespace evmc::literals;
inline constexpr bytes32_t NULL_HASH{
    0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470_bytes32};

inline constexpr bytes32_t NULL_LIST_HASH{
    0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347_bytes32};

// Root hash of an empty trie
inline constexpr bytes32_t NULL_ROOT{
    0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421_bytes32};

MONAD_NAMESPACE_END

namespace boost
{
    inline size_t hash_value(monad::bytes32_t const &bytes) noexcept
    {
        return std::hash<monad::bytes32_t>{}(bytes);
    }
}
