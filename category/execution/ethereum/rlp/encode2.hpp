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
#include <category/core/bit_primitives.hpp>
#include <category/core/rlp/config.hpp>

#include <concepts>
#include <cstring>

MONAD_RLP_NAMESPACE_BEGIN

inline byte_string const EMPTY_STRING = {0x80};

inline byte_string_view zeroless_view(byte_string_view const string_view)
{
    auto const *b = string_view.begin();
    auto const *e = string_view.end();
    while (b < e && *b == 0) {
        ++b;
    }
    return {b, e};
}

inline byte_string to_big_compact(unsigned_integral auto n)
{
    n = bswap(n);
    return byte_string(
        zeroless_view({reinterpret_cast<unsigned char *>(&n), sizeof(n)}));
}

// Same result, reached by looking at words before bytes.
//
// The generic form above byte-swaps the whole value and then walks the leading
// zeros off one `lbu` at a time, which for a 256-bit integer is four
// byte-swaps and up to 32 steps of walking. That is the wrong shape for what
// these values actually are: measured on block 25551991, the average uint256
// RLP field carries **24 leading zero bytes** -- nonces, gas limits, chain
// ids, and values that fit in a word. 35 % of encode_unsigned<uint256_t> was
// swapping words that are entirely zero and 53 % was walking past them, 47
// loop iterations per call.
//
// So: find the top non-zero word (four compares), swap only the words at or
// below it, and take the tail. One `bswap64` instead of four in the common
// case, and no byte walk at all -- countl_zero gives the significant byte
// count of the top word directly.
inline byte_string to_big_compact(uint256_t const &n)
{
    size_t w = uint256_t::num_words;
    while (w != 0 && n[w - 1] == 0) {
        --w;
    }
    if (w == 0) {
        return byte_string{}; // RLP of zero is the empty string
    }
    unsigned const top_bytes =
        8u - static_cast<unsigned>(monad::bits::countl_zero(n[w - 1]) >> 3);
    size_t const len = (w - 1) * 8 + top_bytes;

    // Big-endian, most significant word first: word i lands at offset
    // (w - 1 - i) * 8, so the value occupies be[0, w*8) with (w*8 - len)
    // leading zero bytes in front of it.
    alignas(8) unsigned char be[uint256_t::num_bytes];
    for (size_t i = 0; i < w; ++i) {
        uint64_t const s = monad::bits::bswap64(n[i]);
        std::memcpy(be + (w - 1 - i) * 8, &s, sizeof(s));
    }
    return byte_string{byte_string_view{be + (w * 8 - len), len}};
}

inline byte_string encode_string2(byte_string_view const string_view)
{
    byte_string result;
    uint32_t const size = static_cast<uint32_t>(string_view.size());
    if (size == 1 && string_view[0] <= 0x7f) {
        result = string_view;
    }
    else if (size > 55) {
        auto const size_str = to_big_compact(size);
        MONAD_ASSERT(size_str.size() <= 8u);
        result.push_back(0xb7 + static_cast<unsigned char>(size_str.size()));
        result += size_str;
        result += string_view;
    }
    else {
        result.push_back(0x80 + static_cast<unsigned char>(size));
        result += string_view;
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
        result +=
            (static_cast<unsigned char>(0xf7) +
             static_cast<unsigned char>(size_str.size()));
        result += size_str;
    }
    else {
        result +=
            (static_cast<unsigned char>(0xc0) +
             static_cast<unsigned char>(size));
    }
    ([&] { result += args; }(), ...);
    return result;
}

MONAD_RLP_NAMESPACE_END
