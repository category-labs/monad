#pragma once

#include <monad/config.hpp>

#include <intx/intx.hpp>

#include <concepts>
#include <limits>

MONAD_NAMESPACE_BEGIN

using uint128_t = ::intx::uint128;

static_assert(sizeof(uint128_t) == 16);
static_assert(alignof(uint128_t) == 8);

using uint256_t = ::intx::uint256;

static_assert(sizeof(uint256_t) == 32);
static_assert(alignof(uint256_t) == 8);

using uint512_t = ::intx::uint512;

static_assert(sizeof(uint512_t) == 64);
static_assert(alignof(uint512_t) == 8);

template <class T>
concept unsigned_integral =
    std::unsigned_integral<T> || std::same_as<uint128_t, T> ||
    std::same_as<uint256_t, T> || std::same_as<uint512_t, T>;

inline constexpr uint128_t UINT128_MAX = std::numeric_limits<uint128_t>::max();

inline constexpr uint256_t UINT256_MAX = std::numeric_limits<uint256_t>::max();

inline constexpr uint512_t UINT512_MAX = std::numeric_limits<uint512_t>::max();

using ::intx::to_big_endian;

MONAD_NAMESPACE_END
