#pragma once

#include <monad/rlp/config.hpp>
#include <monad/rlp/util.hpp>

#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>

#include <vector>
#include <concepts>

// To Be Deleted
#include <iostream>

MONAD_RLP_NAMESPACE_BEGIN

// TODO
// is this big enough for payload sizes?
// @tzhi: Not really, since the payload can be as big as uint256, but uint256_t is a intx variable and doesn't have ++method
using byte_string_loc = uint64_t;

inline byte_string_loc decode_length(byte_string_view const enc, byte_string_loc i, byte_string_loc length)
{
    byte_string_loc result = 0;
    for (byte_string_loc j = i; j < i + length; ++j)
    {
        result *= 256;
        result += enc[j];
    }
    return result;
}

inline byte_string decode_string(byte_string_view const enc, byte_string_loc &i)
{
    MONAD_ASSERT(0 <= i && i < enc.size());
    byte_string_loc end;

    const uint8_t &first = enc[i];
    MONAD_ASSERT(first < 192);
    if (first < 128)        // [0, 127]
    {
        end = i + 1;
    }
    else if (first < 184)   // [128, 183]
    {
        ++i;
        const uint8_t length = first - 128;
        end = i + length;
    }
    else                    // [184, 191]
    {
        ++i;
        uint8_t length_of_length = first - 183;
        MONAD_ASSERT(i + length_of_length < enc.size());
        byte_string_loc length = decode_length(enc, i, length_of_length);
        i += length_of_length;
        end = i + length;
    }
    MONAD_ASSERT(end <= enc.size());
    auto dec = byte_string(enc.substr(i, end - i));
    i = end;
    return dec;
}

inline byte_string decode_string(byte_string_view const enc)
{
    byte_string_loc i = 0;
    return decode_string(enc, i);
}

// Tong: Is template here necessary?
template <typename T>
inline std::vector<T> decode_list(byte_string_view const enc)
{
    std::cout << enc.size() << std::endl;
    return {};
}

MONAD_RLP_NAMESPACE_END
