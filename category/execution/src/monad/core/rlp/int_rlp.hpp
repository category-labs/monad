#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/result.hpp>
#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/decode_error.hpp>
#include <monad/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

MONAD_RLP_NAMESPACE_BEGIN

inline byte_string encode_unsigned(unsigned_integral auto const &n)
{
    return encode_string2(to_big_compact(n));
}

template <unsigned_integral T>
constexpr Result<T> decode_unsigned(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto const payload, parse_string_metadata(enc));
    return decode_raw_num<T>(payload);
}

constexpr Result<bool> decode_bool(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto const i, decode_unsigned<uint64_t>(enc));

    if (MONAD_UNLIKELY(i > 1)) {
        return DecodeError::Overflow;
    }

    return i;
}

MONAD_RLP_NAMESPACE_END
