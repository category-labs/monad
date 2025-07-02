#pragma once

#include <monad/config.hpp>

#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>
#include <monad/core/keccak.hpp>

#include <evmc/evmc.hpp>

#include <bit>
#include <cstddef>
#include <functional>

MONAD_NAMESPACE_BEGIN

using bytes32_t = ::evmc::bytes32;

static_assert(sizeof(bytes32_t) == 32);
static_assert(alignof(bytes32_t) == 1);

constexpr bytes32_t to_bytes(uint256_t const n) noexcept
{
    return std::bit_cast<bytes32_t>(n);
}

constexpr bytes32_t to_bytes(hash256 const n) noexcept
{
    return std::bit_cast<bytes32_t>(n);
}

constexpr bytes32_t to_bytes(byte_string_view const data) noexcept
{
    MONAD_ASSERT(data.size() <= sizeof(bytes32_t));

    bytes32_t byte;
    std::copy_n(
        data.begin(),
        data.size(),
        byte.bytes + sizeof(bytes32_t) - data.size());
    return byte;
}

using namespace evmc::literals;
inline constexpr bytes32_t NULL_HASH{
    0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470_bytes32};

inline constexpr bytes32_t NULL_LIST_HASH{
    0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347_bytes32};

// Root hash of an empty trie
inline constexpr bytes32_t NULL_ROOT{
    0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421_bytes32};

inline constexpr bytes32_t NULL_HASH_BLAKE3{
    0xaf1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262_bytes32};

MONAD_NAMESPACE_END

namespace boost
{
    inline size_t hash_value(monad::bytes32_t const &bytes) noexcept
    {
        return std::hash<monad::bytes32_t>{}(bytes);
    }
}
