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
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/decode_error.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>

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
