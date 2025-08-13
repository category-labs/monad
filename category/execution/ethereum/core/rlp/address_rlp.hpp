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
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/decode_error.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

#include <optional>

MONAD_RLP_NAMESPACE_BEGIN

inline byte_string encode_address(std::optional<Address> const &address)
{
    if (!address.has_value()) {
        return byte_string({0x80});
    }
    return encode_string2(to_byte_string_view(address->bytes));
}

inline Result<Address> decode_address(byte_string_view &enc)
{
    Address addr;
    BOOST_OUTCOME_TRY(auto const byte_array, decode_byte_string_fixed<20>(enc));
    std::memcpy(addr.bytes, byte_array.data(), 20);
    return addr;
}

inline Result<std::optional<Address>>
decode_optional_address(byte_string_view &enc)
{
    std::optional<Address> addr;
    BOOST_OUTCOME_TRY(auto const payload, parse_string_metadata(enc));
    if (MONAD_LIKELY(payload.size() == sizeof(Address))) {
        addr = Address{};
        std::memcpy(addr->bytes, payload.data(), sizeof(Address));
    }
    else if (payload.size() > sizeof(Address)) {
        return DecodeError::InputTooLong;
    }
    else if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooShort;
    }

    return addr;
}

MONAD_RLP_NAMESPACE_END
