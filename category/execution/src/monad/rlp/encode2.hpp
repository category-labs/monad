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
    return byte_string(
        zeroless_view({reinterpret_cast<unsigned char *>(&n), sizeof(n)}));
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
        result += (0xf7 + static_cast<unsigned char>(size_str.size()));
        result += size_str;
    }
    else {
        result += (0xc0 + static_cast<unsigned char>(size));
    }
    ([&] { result += args; }(), ...);
    return result;
}

MONAD_RLP_NAMESPACE_END
