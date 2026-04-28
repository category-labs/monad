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
#include <category/core/bytes.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <category/core/rlp/decode_error.hpp>

#include <boost/outcome/try.hpp>

#include <concepts>
#include <type_traits>
#include <utility>

MONAD_RLP_NAMESPACE_BEGIN

template <unsigned_integral T>
inline Result<T> decode_raw_num(byte_string_view const enc)
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

inline Result<size_t> decode_length(byte_string_view const enc)
{
    return decode_raw_num<size_t>(enc);
}

enum class RlpType
{
    String,
    List
};

namespace detail
{

    enum class ParseMetadataOptions
    {
        ReturnRlpType,
    };

    template <ParseMetadataOptions... Options>
    inline constexpr bool should_return_rlp_type =
        ((Options == ParseMetadataOptions::ReturnRlpType) || ...);

    // We want two return versions of the functions below. One which simply
    // returns a byte_string_view when we are parsing/expecting a specific type,
    // e.g. parse_list_metadata. If using the dynamic parse_metadata, we want
    // the result to be a byte_string_view plus the type that was decoded from
    // the first byte of enc, hence when we call
    // parse_string_metadata<ParseMetadataOptions::ReturnRlpType> from
    // parse_metadata, the return value will be an std::pair{RlpType::String,
    // payload}
    template <ParseMetadataOptions... Options>
    using parse_metadata_result_t = std::conditional_t<
        should_return_rlp_type<Options...>,
        Result<std::pair<RlpType, byte_string_view>>, Result<byte_string_view>>;

    template <RlpType Ty, ParseMetadataOptions... Options>
    [[gnu::always_inline]] inline parse_metadata_result_t<Options...>
    extract_payload(byte_string_view &enc, size_t const i, size_t const length)
    {
        auto const end = i + length;

        if (MONAD_UNLIKELY(end > enc.size() || end < i)) {
            return DecodeError::InputTooShort;
        }

        auto const payload = enc.substr(i, length);
        enc = enc.substr(end);

        if constexpr (should_return_rlp_type<Options...>) {
            return {Ty, payload};
        }
        else {
            return payload;
        }
    }

    template <ParseMetadataOptions... Options>
    [[gnu::always_inline]] inline parse_metadata_result_t<Options...>
    parse_string_metadata(byte_string_view &enc)
    {
        MONAD_DEBUG_ASSERT(!enc.empty());
        MONAD_DEBUG_ASSERT(enc[0] < 0xc0);

        size_t i = 0;
        size_t length;

        if (enc[0] < 0x80) // [0x00, 0x7f] - single byte string
        {
            length = 1;
        }
        else if (enc[0] < 0xb8) // [0x80, 0xb7] - short string (0-55 bytes)
        {
            length = enc[0] - 0x80;
            ++i;
        }
        else // [0xb8, 0xbf] - long string, N+1 bytes for length, then
             // payload
        {
            uint8_t const length_of_length = enc[0] - 0xb7;
            ++i;
            if (MONAD_UNLIKELY(i + length_of_length >= enc.size())) {
                return DecodeError::InputTooShort;
            }
            BOOST_OUTCOME_TRY(
                length, decode_length(enc.substr(i, length_of_length)));
            i += length_of_length;
        }
        return extract_payload<RlpType::String, Options...>(enc, i, length);
    }

    template <ParseMetadataOptions... Options>
    [[gnu::always_inline]] inline parse_metadata_result_t<Options...>
    parse_list_metadata(byte_string_view &enc)
    {
        MONAD_DEBUG_ASSERT(!enc.empty());
        MONAD_DEBUG_ASSERT(enc[0] >= 0xc0);

        size_t i = 0;
        size_t length;

        if (enc[0] < 0xf8) // [0xc0, 0xf7] - short list (0-55 bytes)
        {
            length = enc[0] - 0xc0;
            ++i;
        }
        else // [0xf8, 0xff] - long list, N+1 bytes for length, then payload
        {
            uint8_t const length_of_length = enc[0] - 0xf7;
            ++i;
            if (MONAD_UNLIKELY(i + length_of_length >= enc.size())) {
                return DecodeError::InputTooShort;
            }
            BOOST_OUTCOME_TRY(
                length, decode_length(enc.substr(i, length_of_length)));
            i += length_of_length;
        }
        return extract_payload<RlpType::List, Options...>(enc, i, length);
    }
}

inline Result<std::pair<RlpType, byte_string_view>>
parse_metadata(byte_string_view &enc)
{
    if (MONAD_UNLIKELY(enc.empty())) {
        return DecodeError::InputTooShort;
    }
    if (enc[0] < 0xc0) {
        return detail::parse_string_metadata<
            detail::ParseMetadataOptions::ReturnRlpType>(enc);
    }
    else {
        return detail::parse_list_metadata<
            detail::ParseMetadataOptions::ReturnRlpType>(enc);
    }
}

inline Result<byte_string_view> parse_string_metadata(byte_string_view &enc)
{
    if (MONAD_UNLIKELY(enc.empty())) {
        return DecodeError::InputTooShort;
    }
    if (MONAD_UNLIKELY(enc[0] >= 0xc0)) {
        return DecodeError::TypeUnexpected;
    }

    return detail::parse_string_metadata(enc);
}

inline Result<byte_string_view> parse_list_metadata(byte_string_view &enc)
{
    if (MONAD_UNLIKELY(enc.empty())) {
        return DecodeError::InputTooShort;
    }
    if (MONAD_UNLIKELY(enc[0] < 0xc0)) {
        return DecodeError::TypeUnexpected;
    }

    return detail::parse_list_metadata(enc);
}

inline Result<byte_string_view> decode_string(byte_string_view &enc)
{
    return parse_string_metadata(enc);
}

template <size_t N>
inline Result<byte_string_fixed<N>>
decode_byte_string_fixed(byte_string_view &enc)
{
    byte_string_fixed<N> bsf;
    BOOST_OUTCOME_TRY(auto const payload, parse_string_metadata(enc));
    if (MONAD_UNLIKELY(payload.size() != N)) {
        return DecodeError::ArrayLengthUnexpected;
    }
    // NOLINTNEXTLINE(bugprone-suspicious-stringview-data-usage)
    std::memcpy(bsf.data(), payload.data(), N);
    return bsf;
}

MONAD_RLP_NAMESPACE_END
