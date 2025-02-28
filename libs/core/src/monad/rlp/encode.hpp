#pragma once

#include <monad/rlp/config.hpp>

#include <monad/core/byte_string.hpp>
#include <monad/core/cmemory.hpp>
#include <monad/core/likely.h>

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

        union
        {
            size_t n_be;
            unsigned char n_be_bytes[sizeof(size_t)];
        };

        n_be = [&n] {
            if constexpr (std::endian::native == std::endian::little) {
                return std::byteswap(n);
            }
            return n;
        }();
        if (d.size() < sizeof(size_t)) {
#ifdef NDEBUG
            __builtin_unreachable();
#else
            abort();
#endif
        }
        cmemcpy(d.data(), n_be_bytes, sizeof(size_t));
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
encode_list_metadata(std::span<unsigned char> d, size_t const concatenated_size)
{
    if (concatenated_size <= 55) {
        d[0] = 0xC0 + static_cast<unsigned char>(concatenated_size);
        d = d.subspan(1);
    }
    else {
        d[0] = 0xF7 + static_cast<unsigned char>(
                          impl::length_length(concatenated_size));
        d = d.subspan(1);
        d = impl::encode_length(d, concatenated_size);
    }
    return d;
}

constexpr std::span<unsigned char>
encode_list(std::span<unsigned char> d, byte_string_view const s)
{
    d = encode_list_metadata(d, s.size());
    if (d.size() < s.size()) {
#ifdef NDEBUG
        __builtin_unreachable();
#else
        abort();
#endif
    }
    std::memcpy(d.data(), s.data(), s.size());
    return d.subspan(s.size());
}

MONAD_RLP_NAMESPACE_END
