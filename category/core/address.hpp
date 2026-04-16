// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/hex.hpp>

#include <evmc/evmc.h>

#include <ankerl/unordered_dense.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <type_traits>

MONAD_NAMESPACE_BEGIN

struct Address : evmc_address
{
    constexpr Address() noexcept
        : evmc_address{}
    {
    }

    constexpr Address(Address const &) noexcept = default;
    constexpr Address &operator=(Address const &) noexcept = default;

    explicit(false) constexpr Address(evmc_address const &other) noexcept
        : evmc_address{other}
    {
    }

    explicit constexpr Address(uint64_t const v) noexcept
        : evmc_address{}
    {
        for (int i = 0; i < 8; ++i) {
            bytes[19 - i] = static_cast<uint8_t>(v >> (i * 8));
        }
    }

    template <std::same_as<uint8_t>... Bytes>
        requires(sizeof...(Bytes) >= 1 && sizeof...(Bytes) <= 20)
    explicit(false) constexpr Address(Bytes... bs) noexcept
        : evmc_address{{bs...}}
    {
    }

    explicit constexpr operator bool() const noexcept
    {
        return !std::ranges::all_of(bytes, [](auto const b) { return b == 0; });
    }

    // NOLINTNEXTLINE(google-explicit-constructor)
    explicit(false) constexpr operator byte_string_view() const noexcept
    {
        return {bytes, sizeof(bytes)};
    }

    friend constexpr bool
    operator==(Address const &a, Address const &b) noexcept
    {
        return std::equal(a.bytes, a.bytes + 20, b.bytes);
    }

    friend constexpr auto
    operator<=>(Address const &a, Address const &b) noexcept
    {
        return std::lexicographical_compare_three_way(
            a.bytes, a.bytes + 20, b.bytes, b.bytes + 20);
    }
};

static_assert(sizeof(Address) == 20);
static_assert(alignof(Address) == 1);
static_assert(std::is_standard_layout_v<Address>);
static_assert(std::is_trivially_copyable_v<Address>);

constexpr bool is_zero(Address const &addr)
{
    return std::ranges::all_of(addr.bytes, [](auto const b) { return b == 0; });
}

namespace literals
{
    consteval Address operator""_address(char const *const s) noexcept
    {
        return from_hex<Address>(s).value();
    }
}

using literals::operator""_address;

constexpr Address address_from_hex(char const *const s)
{
    return from_hex<Address>(s).value();
}

MONAD_NAMESPACE_END

template <>
struct std::hash<monad::Address>
{
    size_t operator()(monad::Address const &x) const noexcept
    {
        return ankerl::unordered_dense::detail::wyhash::hash(
            x.bytes, sizeof(x.bytes));
    }
};

template <>
struct ankerl::unordered_dense::hash<monad::Address>
{
    using is_avalanching = void;

    uint64_t operator()(monad::Address const &x) const noexcept
    {
        return std::hash<monad::Address>{}(x);
    }
};

namespace boost
{
    inline size_t hash_value(monad::Address const &address) noexcept
    {
        return std::hash<monad::Address>{}(address);
    }
}
