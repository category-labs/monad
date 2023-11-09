#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/encode.hpp>

MONAD_RLP_NAMESPACE_BEGIN

inline byte_string encode_bytes32(bytes32_t const &byte)
{
    return encode_string(to_byte_string_view(byte.bytes));
}

inline byte_string_view
decode_bytes32(bytes32_t &byte, byte_string_view const enc)
{
    return decode_byte_array<32>(byte.bytes, enc);
}

MONAD_RLP_NAMESPACE_END
