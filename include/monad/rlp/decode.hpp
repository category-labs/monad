#pragma once

#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/rlp/config.hpp>

MONAD_RLP_NAMESPACE_BEGIN

template <unsigned_integral T>
constexpr T decode_raw_num(byte_string_view const enc)
{
    MONAD_ASSERT(enc.size() <= sizeof(T));
    T result{};
    std::memcpy(
        &intx::as_bytes(result)[sizeof(T) - enc.size()],
        enc.data(),
        enc.size());
    result = intx::to_big_endian(result);
    return result;
}

constexpr size_t decode_length(byte_string_view const enc)
{
    return decode_raw_num<size_t>(enc);
}

constexpr byte_string_view
parse_string_metadata(byte_string_view &payload, byte_string_view const enc)
{
    size_t i = 0;
    size_t end = 0;

    MONAD_ASSERT(!enc.empty());
    MONAD_ASSERT(enc[0] < 0xc0);
    if (enc[0] < 0x80) // [0x00, 0x7f]
    {
        end = i + 1;
    }
    else if (enc[0] < 0xb8) // [0x80, 0xb7]
    {
        ++i;
        const uint8_t length = enc[0] - 0x80;
        end = i + length;
    }
    else // [0xb8, 0xbf]
    {
        ++i;
        uint8_t length_of_length = enc[0] - 0xb7;
        MONAD_ASSERT(i + length_of_length < enc.size());
        auto const length = decode_length(enc.substr(i, length_of_length));
        i += length_of_length;
        end = i + length;
    }
    MONAD_ASSERT(end <= enc.size());
    payload = enc.substr(i, end - i);
    return enc.substr(end);
}

constexpr byte_string_view
parse_list_metadata(byte_string_view &payload, byte_string_view const enc)
{
    size_t i = 0;
    size_t length;
    ++i;
    MONAD_ASSERT(!enc.empty());
    MONAD_ASSERT(enc[0] >= 0xc0);
    if (enc[0] < 0xf8) {
        length = enc[0] - 0xc0;
    }
    else {
        size_t const length_of_length = enc[0] - 0xf7;
        MONAD_ASSERT(i + length_of_length < enc.size());

        length = decode_length(enc.substr(i, length_of_length));
        i += length_of_length;
    }
    auto const end = i + length;
    MONAD_ASSERT(end <= enc.size());

    payload = enc.substr(i, end - i);
    return enc.substr(end, enc.size() - end);
}

template <size_t size>
constexpr byte_string_view
decode_byte_array(uint8_t bytes[size], byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_string_metadata(payload, enc);
    MONAD_ASSERT(payload.size() == size);
    std::memcpy(bytes, payload.data(), size);
    return rest_of_enc;
}

constexpr byte_string_view
decode_string(byte_string &str, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_string_metadata(payload, enc);
    str = byte_string(payload);
    return rest_of_enc;
}

template <size_t N>
byte_string_view
decode_byte_string_fixed(byte_string_fixed<N> &data, byte_string_view const enc)
{
    return decode_byte_array<N>(data.data(), enc);
}

MONAD_RLP_NAMESPACE_END
