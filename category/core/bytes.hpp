// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/core/config.hpp>

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>

#include <evmc/evmc.hpp>

#include <ankerl/unordered_dense.h>

#include <algorithm>
#include <bit>
#include <cstddef>
#include <functional>

MONAD_NAMESPACE_BEGIN

struct bytes32_t : evmc_bytes32
{
    constexpr bytes32_t() noexcept
        : evmc_bytes32{}
    {
    }

    constexpr bytes32_t(bytes32_t const &) noexcept = default;
    constexpr bytes32_t &operator=(bytes32_t const &) noexcept = default;

    explicit(false) constexpr bytes32_t(evmc_bytes32 const &other) noexcept
        : evmc_bytes32{other}
    {
    }

    explicit constexpr bytes32_t(uint64_t const v) noexcept
        : evmc_bytes32{}
    {
        for (int i = 0; i < 8; ++i) {
            bytes[31 - i] = static_cast<uint8_t>(v >> (i * 8));
        }
    }

    template <std::same_as<uint8_t>... Bytes>
        requires(sizeof...(Bytes) >= 1 && sizeof...(Bytes) <= 32)
    explicit(false) constexpr bytes32_t(Bytes... bs) noexcept
        : evmc_bytes32{{bs...}}
    {
    }

    explicit constexpr operator bool() const noexcept
    {
        return std::any_of(bytes, bytes + 32, [](uint8_t b) { return b != 0; });
    }

    // NOLINTNEXTLINE(google-explicit-constructor)
    explicit(false) constexpr operator byte_string_view() const noexcept
    {
        return {bytes, sizeof(bytes)};
    }

    friend constexpr bool
    operator==(bytes32_t const &a, bytes32_t const &b) noexcept
    {
        return std::equal(a.bytes, a.bytes + 32, b.bytes);
    }

    friend constexpr auto
    operator<=>(bytes32_t const &a, bytes32_t const &b) noexcept
    {
        return std::lexicographical_compare_three_way(
            a.bytes, a.bytes + 32, b.bytes, b.bytes + 32);
    }
};

static_assert(sizeof(bytes32_t) == 32);
static_assert(alignof(bytes32_t) == 1);

using uint256_be_t = bytes32_t;

constexpr bytes32_t to_bytes(uint256_t const &n) noexcept
{
    return std::bit_cast<bytes32_t>(n);
}

constexpr bytes32_t to_bytes(hash256 const &n) noexcept
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

namespace literals
{
    consteval bytes32_t operator""_bytes32(char const *const s) noexcept
    {
        return from_hex<bytes32_t>(s).value();
    }
}

using literals::operator""_bytes32;

constexpr bytes32_t bytes32_from_hex(char const *const s)
{
    return from_hex<bytes32_t>(s).value();
}

constexpr bytes32_t NULL_HASH{bytes32_from_hex(
    "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")};

constexpr bytes32_t NULL_LIST_HASH{bytes32_from_hex(
    "1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347")};

// Root hash of an empty trie
constexpr bytes32_t NULL_ROOT{bytes32_from_hex(
    "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")};

constexpr bytes32_t NULL_HASH_BLAKE3{bytes32_from_hex(
    "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262")};

MONAD_NAMESPACE_END

template <>
struct std::hash<monad::bytes32_t>
{
    size_t operator()(monad::bytes32_t const &x) const noexcept
    {
        return ankerl::unordered_dense::detail::wyhash::hash(
            x.bytes, sizeof(x.bytes));
    }
};

template <>
struct ankerl::unordered_dense::hash<monad::bytes32_t>
{
    using is_avalanching = void;

    uint64_t operator()(monad::bytes32_t const &x) const noexcept
    {
        return std::hash<monad::bytes32_t>{}(x);
    }
};

namespace boost
{
    inline size_t hash_value(monad::bytes32_t const &bytes) noexcept
    {
        return std::hash<monad::bytes32_t>{}(bytes);
    }
}
