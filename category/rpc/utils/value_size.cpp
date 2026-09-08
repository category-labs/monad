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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/rpc/utils/value_size.hpp>

#include <bit>
#include <cstddef>
#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

size_t value_size(size_t x)
{
    // The image of bit_width is [0, 64] for size_t on typical platforms, so it
    // is safe to interpret its return value as an element of size_t.
    return x == 0 ? 3 : 2 + (static_cast<size_t>(std::bit_width(x)) + 3) / 4;
}

size_t value_size(uint256_t const &x)
{
    return x == 0 ? 3 : 2 + (monad::bit_width(x) + 3) / 4;
}

size_t value_size(Address const &)
{
    return 2 * sizeof(Address) + 2 /* 0xABCDEF.... */;
}

size_t value_size(bytes32_t const &)
{
    return 2 * sizeof(bytes32_t) + 2 /* 0xABCDEF.... */;
}

size_t value_size(byte_string_view const &x)
{
    return x.size() * 2 + 2 /* 0xABCDEF.... */;
}

size_t value_size(byte_string const &x)
{
    return x.size() * 2 + 2 /* 0xABCDEF.... */;
}

size_t value_size(byte_string_fixed<8> const &)
{
    return 18; // 0x0000...
}

size_t value_size(byte_string_fixed<256> const &)
{
    return 514; // 0x0000...
}

size_t value_size(std::optional<Address> const &x)
{
    if (x.has_value()) {
        return value_size(x.value());
    }
    else {
        return 3; // 0x0
    }
}

size_t value_size(std::optional<bytes32_t> const &x)
{
    if (x.has_value()) {
        return value_size(x.value());
    }
    else {
        return 3; // 0x0
    }
}

size_t value_size(std::optional<uint64_t> const &x)
{
    if (x.has_value()) {
        return value_size(x.value());
    }
    else {
        return 3; // 0x0
    }
}

size_t value_size(std::optional<uint256_t> const &x)
{
    if (x.has_value()) {
        return value_size(x.value());
    }
    else {
        return 3; // 0x0
    }
}

MONAD_NAMESPACE_END
