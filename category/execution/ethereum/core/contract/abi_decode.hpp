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
#include <category/core/config.hpp>
#include <category/core/math.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/abi_decode_error.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>

#include <cstring>
#include <type_traits>

#include <boost/outcome/try.hpp>

MONAD_NAMESPACE_BEGIN

// All solidity uints are are left padded to fit in 32 bytes. An address is
// treated as a uint160 by the encoder. All fixed sized bytes go in the "head".
// https://docs.soliditylang.org/en/latest/abi-spec.html
//
// Note that this only errors out when the input is too short. Note that any
// dirty higher order bits are ignored and not checked for overflow. This is in
// line with solidity's behavior as of version 0.5.0
//
// https://docs.soliditylang.org/en/v0.8.30/050-breaking-changes.html
template <typename T>
    requires(BigEndianType<T> || std::same_as<T, Address>)
Result<T> abi_decode_fixed(byte_string_view &enc)
{
    static_assert(sizeof(T) <= 32);
    if (MONAD_UNLIKELY(enc.size() < 32)) {
        return AbiDecodeError::InputTooShort;
    }

    constexpr size_t offset = 32 - sizeof(T);
    T output{};
    std::memcpy(&output, enc.data() + offset, sizeof(T));
    enc.remove_prefix(32);
    return output;
}

// Dynamic sized data goes in the "tail". Note that for precompiles, we always
// know the size of the bytes we are reading in, which is why we return a fixed
// size byte string.
//
// The expectation for using this API is to simply skip over the user provided
// offsets in the head, look for bytes of an expected length in the tail.
template <size_t N>
Result<byte_string_fixed<N>> abi_decode_bytes_tail(byte_string_view &enc)
{
    static_assert(N > 32, "bytesN (N<=32) belongs in head");

    BOOST_OUTCOME_TRY(auto const length, abi_decode_fixed<u256_be>(enc));
    if (MONAD_UNLIKELY(length.native() != N)) {
        return AbiDecodeError::LengthMismatch;
    }

    constexpr size_t padded = round_up(N, 32uz);
    if (MONAD_UNLIKELY(enc.size() < padded)) {
        return AbiDecodeError::InputTooShort;
    }

    byte_string_fixed<N> output{};
    std::memcpy(output.data(), enc.data(), N);
    enc.remove_prefix(padded);
    return output;
}

MONAD_NAMESPACE_END
