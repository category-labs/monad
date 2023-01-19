#pragma once

#include <monad/config.hpp>

#include <intx/intx.hpp>

#include <concepts>

MONAD_NAMESPACE_BEGIN

using uint128_t = ::intx::uint128;

static_assert(sizeof(uint128_t) == 16);
static_assert(alignof(uint128_t) == 8);

using uint256_t = ::intx::uint256;

static_assert(sizeof(uint256_t) == 32);
static_assert(alignof(uint256_t) == 8);

template <class T>
concept unsigned_integral =
    std::unsigned_integral<T> || std::same_as<uint256_t, T> ||
    std::same_as<uint128_t, T>;

MONAD_NAMESPACE_END
