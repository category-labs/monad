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

#include <category/core/byte_string.hpp>
#include <category/core/endian.hpp>
#include <category/core/likely.h>
#include <category/core/rlp/config.hpp>
#include <category/core/unaligned.hpp>

#include <algorithm>
#include <bit>
#include <cstddef>
#include <cstring>
#include <span>

MONAD_RLP_NAMESPACE_BEGIN

namespace impl
{
    constexpr size_t length_length(size_t const n)
    {
        size_t const lz_bits = static_cast<size_t>(std::countl_zero(n));
        size_t const lz_bytes = lz_bits / 8;
        return sizeof(size_t) - lz_bytes;
    }

    /**
     * always stores sizeof(size_t) bytes
     */
    constexpr std::span<unsigned char>
    encode_length(std::span<unsigned char> d, size_t n)
    {
        size_t const lz_bits = static_cast<size_t>(std::countl_zero(n));
        size_t const lz_bytes = lz_bits / 8;
        if (MONAD_LIKELY(n != 0)) {
            n <<= lz_bytes * 8;
        }

        size_t const n_be = std::byteswap(n);
        if (d.size() < sizeof(size_t)) {
#ifdef NDEBUG
            __builtin_unreachable();
#else
            abort();
#endif
        }
        unaligned_store(d.data(), n_be);
        return d.subspan((sizeof(size_t) - lz_bytes));
    }
}

/**
 * max return value is 1 + sizeof(size_t) + s.size()
 */
constexpr size_t string_length(byte_string_view const s)
{
    if (s.size() == 1 and s[0] <= 0x7F) {
        return 1;
    }
    else if (s.size() <= 55) {
        return 1 + s.size();
    }
    else {
        return 1 + impl::length_length(s.size()) + s.size();
    }
}

constexpr std::span<unsigned char>
encode_string(std::span<unsigned char> d, byte_string_view const s)
{
    if (s.size() == 1 and s[0] <= 0x7F) {
        d[0] = s[0];
        d = d.subspan(1);
    }
    else if (s.size() <= 55) {
        d[0] = 0x80 + static_cast<unsigned char>(s.size());
        d = d.subspan(1);
        if (d.size() < s.size()) {
#ifdef NDEBUG
            __builtin_unreachable();
#else
            abort();
#endif
        }
        std::memcpy(d.data(), s.data(), s.size());
        d = d.subspan(s.size());
    }
    else {
        d[0] = 0xB7 + static_cast<unsigned char>(impl::length_length(s.size()));
        d = d.subspan(1);
        d = impl::encode_length(d, s.size());
        if (d.size() < s.size()) {
#ifdef NDEBUG
            __builtin_unreachable();
#else
            abort();
#endif
        }
        std::memcpy(d.data(), s.data(), s.size());
        d = d.subspan(s.size());
    }
    return d;
}

/**
 * max return value is 1 + sizeof(size_t) + s.size()
 */
constexpr size_t list_length(size_t const concatenated_size)
{
    if (concatenated_size <= 55) {
        return 1 + concatenated_size;
    }
    else {
        return 1 + impl::length_length(concatenated_size) + concatenated_size;
    }
}

constexpr std::span<unsigned char>
encode_list(std::span<unsigned char> d, byte_string_view const s)
{
    if (s.size() <= 55) {
        d[0] = 0xC0 + static_cast<unsigned char>(s.size());
        d = d.subspan(1);
        if (d.size() < s.size()) {
#ifdef NDEBUG
            __builtin_unreachable();
#else
            abort();
#endif
        }
        std::memcpy(d.data(), s.data(), s.size());
        d = d.subspan(s.size());
    }
    else {
        d[0] = 0xF7 + static_cast<unsigned char>(impl::length_length(s.size()));
        d = d.subspan(1);
        d = impl::encode_length(d, s.size());
        if (d.size() < s.size()) {
#ifdef NDEBUG
            __builtin_unreachable();
#else
            abort();
#endif
        }
        std::memcpy(d.data(), s.data(), s.size());
        d = d.subspan(s.size());
    }
    return d;
}

MONAD_RLP_NAMESPACE_END
