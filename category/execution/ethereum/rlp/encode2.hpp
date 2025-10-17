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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/int.hpp>
#include <category/core/rlp/config.hpp>

#include <concepts>

MONAD_RLP_NAMESPACE_BEGIN

inline byte_string const EMPTY_STRING = {0x80};

inline byte_string_view zeroless_view(byte_string_view const string_view)
{
    auto b = string_view.begin();
    auto const e = string_view.end();
    while (b < e && *b == 0) {
        ++b;
    }
    return {b, e};
}

inline byte_string to_big_compact(unsigned_integral auto n)
{
    n = intx::to_big_endian(n);
    return to_byte_string(
        zeroless_view({reinterpret_cast<unsigned char *>(&n), sizeof(n)}));
}

inline byte_string encode_string2(byte_string_view const string_view)
{
    byte_string result;
    uint32_t const size = static_cast<uint32_t>(string_view.size());
    if (size == 1 && string_view[0] <= 0x7f) {
        result.assign(string_view.begin(), string_view.end());
    }
    else if (size > 55) {
        auto const size_str = to_big_compact(size);
        MONAD_ASSERT(size_str.size() <= 8u);
        result.push_back(
            static_cast<unsigned char>(0xb7 + size_str.size()));
        append_bytes(result, to_byte_string_view(size_str));
        append_bytes(result, string_view);
    }
    else {
        result.push_back(
            static_cast<unsigned char>(0x80 + size));
        append_bytes(result, string_view);
    }
    return result;
}

template <std::convertible_to<byte_string>... Args>
byte_string encode_list2(Args const &...args)
{
    size_t size = 0;
    ([&] { size += args.size(); }(), ...);
    byte_string result;
    if (size > 55) {
        auto const size_str = to_big_compact(size);
        MONAD_ASSERT(size_str.size() <= 8u);
        result.push_back(
            static_cast<unsigned char>(0xf7 + size_str.size()));
        append_bytes(result, to_byte_string_view(size_str));
    }
    else {
        result.push_back(
            static_cast<unsigned char>(0xc0 + size));
    }
    ([&] {
        result.insert(result.end(), args.begin(), args.end());
    }(), ...);
    return result;
}

MONAD_RLP_NAMESPACE_END
