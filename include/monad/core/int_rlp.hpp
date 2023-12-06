#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>
#include <monad/core/result.hpp>
#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

MONAD_RLP_NAMESPACE_BEGIN

inline byte_string encode_unsigned(unsigned_integral auto const &n)
{
    return encode_string2(to_big_compact(n));
}

template <unsigned_integral T>
constexpr Result<byte_string_view>
decode_unsigned(T &u_num, byte_string_view const enc)
{
    byte_string_view payload{};
    BOOST_OUTCOME_TRY(
        auto const rest_of_enc, parse_string_metadata(payload, enc));
    BOOST_OUTCOME_TRY(u_num, decode_raw_num<T>(payload));
    return rest_of_enc;
}

constexpr Result<byte_string_view>
decode_bool(bool &target, byte_string_view const enc)
{
    uint64_t i{0};
    BOOST_OUTCOME_TRY(auto const ret, decode_unsigned<uint64_t>(i, enc));
    MONAD_DEBUG_ASSERT(i <= 1);
    target = i;
    return ret;
}

MONAD_RLP_NAMESPACE_END
