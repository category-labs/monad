#pragma once

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <category/execution/ethereum/rlp/decode_error.hpp>

#include <boost/outcome/try.hpp>

MONAD_RLP_NAMESPACE_BEGIN

template <unsigned_integral T>
constexpr Result<T> decode_raw_num(byte_string_view const enc)
{
    if (MONAD_UNLIKELY(enc.size() > sizeof(T))) {
        return DecodeError::Overflow;
    }

    if (enc.empty()) {
        return 0;
    }

    if (enc[0] == 0) {
        return DecodeError::LeadingZero;
    }

    T result{};
    std::memcpy(
        &intx::as_bytes(result)[sizeof(T) - enc.size()],
        enc.data(),
        enc.size());
    result = intx::to_big_endian(result);
    return result;
}

constexpr Result<size_t> decode_length(byte_string_view const enc)
{
    return decode_raw_num<size_t>(enc);
}

constexpr Result<byte_string_view> parse_string_metadata(byte_string_view &enc)
{
    size_t i = 0;
    size_t end = 0;

    if (MONAD_UNLIKELY(enc.empty())) {
        return DecodeError::InputTooShort;
    }

    if (MONAD_UNLIKELY(enc[0] >= 0xc0)) {
        return DecodeError::TypeUnexpected;
    }

    if (enc[0] < 0x80) // [0x00, 0x7f]
    {
        end = i + 1;
    }
    else if (enc[0] < 0xb8) // [0x80, 0xb7]
    {
        ++i;
        uint8_t const length = enc[0] - 0x80;
        end = i + length;
    }
    else // [0xb8, 0xbf]
    {
        ++i;
        uint8_t length_of_length = enc[0] - 0xb7;

        if (MONAD_UNLIKELY(i + length_of_length >= enc.size())) {
            return DecodeError::InputTooShort;
        }

        BOOST_OUTCOME_TRY(
            auto const length, decode_length(enc.substr(i, length_of_length)));
        i += length_of_length;
        end = i + length;
    }

    if (MONAD_UNLIKELY(end > enc.size())) {
        return DecodeError::InputTooShort;
    }

    auto const payload = enc.substr(i, end - i);
    enc = enc.substr(end);
    return payload;
}

constexpr Result<byte_string_view> parse_list_metadata(byte_string_view &enc)
{
    size_t i = 0;
    size_t length;
    ++i;

    if (MONAD_UNLIKELY(enc.empty())) {
        return DecodeError::InputTooShort;
    }

    if (MONAD_UNLIKELY(enc[0] < 0xc0)) {
        return DecodeError::TypeUnexpected;
    }

    if (enc[0] < 0xf8) {
        length = enc[0] - 0xc0;
    }
    else {
        size_t const length_of_length = enc[0] - 0xf7;

        if (MONAD_UNLIKELY(i + length_of_length >= enc.size())) {
            return DecodeError::InputTooShort;
        }

        BOOST_OUTCOME_TRY(
            length, decode_length(enc.substr(i, length_of_length)));
        i += length_of_length;
    }
    auto const end = i + length;

    if (MONAD_UNLIKELY(end > enc.size())) {
        return DecodeError::InputTooShort;
    }

    auto const payload = enc.substr(i, end - i);
    enc = enc.substr(end);
    return payload;
}

constexpr Result<byte_string_view> decode_string(byte_string_view &enc)
{
    return parse_string_metadata(enc);
}

template <size_t N>
constexpr Result<byte_string_fixed<N>>
decode_byte_string_fixed(byte_string_view &enc)
{
    byte_string_fixed<N> bsf;
    BOOST_OUTCOME_TRY(auto const payload, parse_string_metadata(enc));
    if (MONAD_UNLIKELY(payload.size() != N)) {
        return DecodeError::ArrayLengthUnexpected;
    }
    std::memcpy(bsf.data(), payload.data(), N);
    return bsf;
}

MONAD_RLP_NAMESPACE_END
