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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>

#include <evmc/evmc.hpp>

#include <ankerl/unordered_dense.h>

#include <algorithm>
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

template <>
struct ankerl::unordered_dense::hash<monad::bytes32_t>
{
    using is_avalanching = void;

    uint64_t operator()(monad::bytes32_t const &x) const noexcept
    {
        return detail::wyhash::hash(x.bytes, sizeof(x.bytes));
    }
};

namespace boost
{
    inline size_t hash_value(monad::bytes32_t const &bytes) noexcept
    {
        return std::hash<monad::bytes32_t>{}(bytes);
    }
}
