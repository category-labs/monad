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

#include <bit>
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
// below it, and take the tail. One `bswap` instead of four in the common
// case, and no byte walk at all -- std::countl_zero gives the significant
// byte count of the top word directly.
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
        8u - static_cast<unsigned>(std::countl_zero(n[w - 1]) >> 3);
    size_t const len = (w - 1) * 8 + top_bytes;

    // Big-endian, most significant word first: word i lands at offset
    // (w - 1 - i) * 8, so the value occupies be[0, w*8) with (w*8 - len)
    // leading zero bytes in front of it.
    alignas(8) unsigned char be[uint256_t::num_bytes];
    for (size_t i = 0; i < w; ++i) {
        uint64_t const s = bswap(n[i]);
        std::memcpy(be + (w - 1 - i) * 8, &s, sizeof(s));
    }
    return byte_string{byte_string_view{be + (w * 8 - len), len}};
}

// RLP in two halves: three functions that answer "how long would that be"
// without building it, and three that write into a caller's buffer instead of
// returning a fresh one. This is where the encoding lives. encode_string2 and
// encode_list2 below are their first callers, and the 0x7f, 0x80, 0xb7, 0xc0
// and 0xf7 boundaries appear nowhere else.
//
// Every RLP structure knows its own lengths -- a list's is the sum of its
// children's -- so a caller that reaches for these directly sizes one buffer
// and writes each byte exactly once, rather than materialising every nested
// list so that its parent can measure it. receipt_rlp.cpp does.

// to_big_compact's length. Built-in types only: uint128_t and uint256_t satisfy
// the concept above but not std::bit_width, and an overload for them belongs
// beside to_big_compact's own if one is ever wanted.
inline size_t big_compact_size(std::unsigned_integral auto const n)
{
    return (static_cast<size_t>(std::bit_width(n)) + 7) / 8;
}

// The length of the header encode_list2 writes ahead of a payload this size.
inline size_t list_header_size(size_t const payload)
{
    return payload > 55 ? 1 + big_compact_size(payload) : 1;
}

// encode_string2's length, header included.
inline size_t encoded_string_size(byte_string_view const string_view)
{
    size_t const size = string_view.size();
    if (size == 1 && string_view[0] <= 0x7f) {
        return 1;
    }
    return (size > 55 ? 1 + big_compact_size(size) : 1) + size;
}

// A long-form length: the prefix byte, which carries the count of the bytes
// after it, then the length itself big-endian.
inline void
append_length(unsigned char *&p, unsigned char const base, size_t const size)
{
    size_t const n = big_compact_size(size);
    *p++ = static_cast<unsigned char>(base + n);
    for (size_t i = n; i-- > 0;) {
        *p++ = static_cast<unsigned char>(size >> (i * 8));
    }
}

// encode_list2's header, written ahead of a payload the caller owns.
inline void append_list_header(unsigned char *&p, size_t const payload)
{
    if (payload > 55) {
        append_length(p, 0xf7, payload);
        return;
    }
    *p++ = static_cast<unsigned char>(0xc0 + payload);
}

// encode_string2, appended rather than returned.
inline void
append_string2(unsigned char *&p, byte_string_view const string_view)
{
    size_t const size = string_view.size();
    if (size == 1 && string_view[0] <= 0x7f) {
        *p++ = string_view[0];
        return;
    }
    if (size > 55) {
        append_length(p, 0xb7, size);
    }
    else {
        *p++ = static_cast<unsigned char>(0x80 + size);
    }
    std::memcpy(p, string_view.data(), size);
    p += size;
}

inline byte_string encode_string2(byte_string_view const string_view)
{
    byte_string result;
    result.resize_and_overwrite(
        encoded_string_size(string_view),
        [string_view](unsigned char *const buf, size_t const n) {
            unsigned char *p = buf;
            append_string2(p, string_view);
            MONAD_ASSERT(p == buf + n);
            return n;
        });
    return result;
}

template <std::convertible_to<byte_string>... Args>
byte_string encode_list2(Args const &...args)
{
    size_t payload = 0;
    ([&] { payload += args.size(); }(), ...);

    byte_string result;
    result.resize_and_overwrite(
        list_header_size(payload) + payload,
        [&](unsigned char *const buf, size_t const n) {
            unsigned char *p = buf;
            append_list_header(p, payload);
            auto const put = [&p](auto const &a) {
                std::memcpy(p, a.data(), a.size());
                p += a.size();
            };
            (put(args), ...);
            MONAD_ASSERT(p == buf + n);
            return n;
        });
    return result;
}

MONAD_RLP_NAMESPACE_END
