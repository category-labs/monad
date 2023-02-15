#pragma once

#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>

MONAD_NAMESPACE_BEGIN

template <unsigned_integral T>
inline constexpr T decode_raw_num(byte_string_view const enc)
{
    MONAD_ASSERT(enc.size() < max_byte_string_loc);
    T result{};
    std::memcpy(
        &intx::as_bytes(result)[sizeof(T) - enc.size()],
        enc.data(),
        enc.size());
    result = intx::to_big_endian(result);
    return result;
}

inline constexpr byte_string_loc decode_length(byte_string_view const enc)
{
    return decode_raw_num<byte_string_loc>(enc);
}

inline constexpr byte_string_view
parse_string_metadata(byte_string_view &payload, byte_string_view const enc)
{
    MONAD_ASSERT(enc.size() < max_byte_string_loc);
    byte_string_loc i = 0;
    byte_string_loc end{};

    const uint8_t &first = enc[i];
    MONAD_ASSERT(first < 0xc0);
    if (first < 0x80) // [0x00, 0x7f]
    {
        end = i + 1;
    }
    else if (first < 0xb8) // [0x80, 0xb7]
    {
        ++i;
        const uint8_t length = first - 0x80;
        end = i + length;
    }
    else // [0xb8, 0xbf]
    {
        ++i;
        uint8_t length_of_length = first - 0xb7;
        MONAD_ASSERT(i + length_of_length < enc.size());
        byte_string_loc length = decode_length(enc.substr(i, length_of_length));
        i += length_of_length;
        end = i + length;
    }
    MONAD_ASSERT(end <= enc.size());
    payload = enc.substr(i, end - i);
    return enc.substr(end);
}

inline constexpr byte_string_view
parse_list_metadata(byte_string_view &payload, byte_string_view const enc)
{
    MONAD_ASSERT(0 < enc.size() && enc.size() < max_byte_string_loc);

    byte_string_loc i = 0;
    byte_string_loc length{};
    const uint8_t &first = enc[i];
    ++i;
    MONAD_ASSERT(first >= 0xc0);
    if (first < 0xf8) {
        length = first - 0xc0;
    }
    else {
        byte_string_loc length_of_length = first - 0xf7;
        MONAD_ASSERT(i + length_of_length < enc.size());

        length = decode_length(enc.substr(i, length_of_length));
        i += length_of_length;
    }
    const byte_string_loc end = i + length;
    MONAD_ASSERT(end <= enc.size());

    payload = enc.substr(i, end - i);
    return enc.substr(end, enc.size() - end);
}

template <size_t size>
inline constexpr byte_string_view
decode_byte_array(uint8_t bytes[size], byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_string_metadata(payload, enc);
    MONAD_ASSERT(payload.size() == size);
    std::memcpy(bytes, payload.data(), size);
    return rest_of_enc;
}

inline byte_string_view zeroless_view(byte_string_view const s)
{
    auto b = s.begin();
    auto const e = s.end();
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

MONAD_NAMESPACE_END
