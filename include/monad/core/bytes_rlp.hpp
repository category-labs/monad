#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/encode.hpp>

MONAD_RLP_NAMESPACE_BEGIN

inline byte_string encode_bytes32(bytes32_t const &b)
{
    return encode_string(to_byte_string_view(b.bytes));
}

inline byte_string_view
decode_bytes32(bytes32_t &bytes, byte_string_view const enc)
{
    return decode_byte_array<32>(bytes.bytes, enc);
}

MONAD_RLP_NAMESPACE_END
