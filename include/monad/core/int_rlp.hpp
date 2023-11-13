#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>
#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/encode2.hpp>

MONAD_RLP_NAMESPACE_BEGIN

inline byte_string encode_unsigned(unsigned_integral auto const &n)
{
    return encode_string2(to_big_compact(n));
}

template <unsigned_integral T>
constexpr byte_string_view decode_unsigned(T &u_num, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_string_metadata(payload, enc);
    u_num = decode_raw_num<T>(payload);
    return rest_of_enc;
}

constexpr byte_string_view decode_bool(bool &target, byte_string_view const enc)
{
    uint64_t i{0};
    auto ret = decode_unsigned<uint64_t>(i, enc);
    MONAD_DEBUG_ASSERT(i <= 1);
    target = i;
    return ret;
}

MONAD_RLP_NAMESPACE_END
