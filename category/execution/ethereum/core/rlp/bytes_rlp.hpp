#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>

MONAD_RLP_NAMESPACE_BEGIN

inline byte_string encode_bytes32(bytes32_t const &byte)
{
    return encode_string2(to_byte_string_view(byte.bytes));
}

inline byte_string encode_bytes32_compact(bytes32_t const &byte)
{
    return encode_string2(zeroless_view(to_byte_string_view(byte.bytes)));
}

inline Result<bytes32_t> decode_bytes32(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto const byte_array, decode_byte_string_fixed<32>(enc));
    return to_bytes(to_byte_string_view(byte_array));
}

inline Result<bytes32_t> decode_bytes32_compact(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto const byte_array, decode_string(enc));
    return to_bytes(byte_array);
}

MONAD_RLP_NAMESPACE_END
