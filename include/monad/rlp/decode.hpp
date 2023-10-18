#pragma once

#include <monad/rlp/config.hpp>
#include <monad/rlp/decode_error.hpp>
#include <monad/rlp/util.hpp>

#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>

#include <boost/outcome/try.hpp>

MONAD_RLP_NAMESPACE_BEGIN

inline constexpr DecodeResult
decode_string(byte_string &str, byte_string_view const enc)
{
    byte_string_view payload{};
    BOOST_OUTCOME_TRY(
        auto const rest_of_enc, parse_string_metadata(payload, enc));
    str = byte_string(payload);
    return rest_of_enc;
}

MONAD_RLP_NAMESPACE_END
