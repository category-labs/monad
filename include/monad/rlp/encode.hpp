#pragma once

#include <monad/rlp/config.hpp>
#include <monad/rlp/util.hpp>

#include <monad/core/byte_string.hpp>

#include <concepts>

MONAD_RLP_NAMESPACE_BEGIN

inline byte_string encode_string(byte_string_view const str)
{
    byte_string result;
    uint32_t const size = str.size();
    if (size == 1 && str[0] <= 0x7f) {
        result = str;
    }
    else if (size > 55) {
        auto const size_str = to_big_compact(size);
        result.push_back(0xb7 + size_str.size());
        result += size_str;
        result += str;
    }
    else {
        result.push_back(0x80 + size);
        result += str;
    }
    return result;
}

template <std::convertible_to<byte_string>... Args>
inline byte_string encode_list(Args const &...args)
{
    size_t size = 0;
    ([&] { size += args.size(); }(), ...);
    byte_string result;
    if (size > 55) {
        auto const size_str = to_big_compact(size);
        result += (0xf7 + size_str.size());
        result += size_str;
    }
    else {
        result += (0xc0 + size);
    }
    ([&] { result += args; }(), ...);
    return result;
}

MONAD_RLP_NAMESPACE_END
