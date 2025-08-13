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
