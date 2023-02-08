#pragma once

#include <monad/rlp/config.hpp>
#include <monad/rlp/util.hpp>

#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>

#include <concepts>

MONAD_RLP_NAMESPACE_BEGIN

// is this big enough for payload sizes?
using byte_string_loc = uint64_t;

inline byte_string_loc decode_unsigned(byte_string_view const enc, byte_string_loc i, byte_string_loc length)
{
    byte_string_loc result = 0;
    for (byte_string_loc j = i; j < i + length; ++j)
    {
        result *= 256;
        result += enc[j];
    }
    return result;
}

inline std::pair<byte_string, byte_string_loc> decode_string(byte_string_view const enc, byte_string_loc i)
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
        byte_string_loc length = decode_unsigned(enc, i, length_of_length);
        i += length_of_length;
        end = i + length;
    }
    MONAD_ASSERT(end <= enc.size());
    return std::make_pair(byte_string(enc.substr(i, end)), end);
}

inline byte_string decode_string(byte_string_view const enc)
{
    return decode_string(enc, 0).first;
}

MONAD_RLP_NAMESPACE_END
