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
#include <category/core/rlp/decode_error.hpp>
#include <category/core/rlp/encode.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

#include <span>

MONAD_RLP_NAMESPACE_BEGIN

inline byte_string encode_unsigned(unsigned_integral auto const &n)
{
    return encode_string2(to_big_compact(n));
}

// Encode into the start of dest and return the unused tail. At most
// 1 + sizeof(n) bytes are written; no temporary byte_string is constructed.
inline std::span<unsigned char>
encode_unsigned(std::span<unsigned char> dest, unsigned_integral auto const &n)
{
    auto const big_endian = bswap(n);
    return encode_string(
        dest, zeroless_view({as_bytes(big_endian), sizeof(big_endian)}));
}

#ifdef MONAD_ZKVM_ZISK
// Count leading zero bytes directly instead of scanning them.
inline std::span<unsigned char>
encode_unsigned(std::span<unsigned char> dest, uint64_t const n)
{
    uint64_t const big_endian = bswap(n);
    unsigned const zero_bytes = static_cast<unsigned>(std::countl_zero(n)) >> 3;
    return encode_string(
        dest, {as_bytes(big_endian) + zero_bytes, 8u - zero_bytes});
}
#endif

template <unsigned_integral T>
inline Result<T> decode_unsigned(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto const payload, parse_string_metadata(enc));
    return decode_raw_num<T>(payload);
}
#ifdef MONAD_ZKVM_ZISK

// Decode canonical integers into out without a Result<T> temporary.
// Fall back to decode_unsigned for other inputs to preserve its errors.
template <unsigned_integral T>
[[gnu::always_inline]] inline Result<void>
decode_unsigned_into(byte_string_view &enc, T &out)
{
    if (MONAD_LIKELY(!enc.empty())) {
        unsigned char const b = enc[0];
        if (b < 0x80) {
            if (MONAD_LIKELY(b != 0)) {
                out = T{b};
                enc.remove_prefix(1);
                return BOOST_OUTCOME_V2_NAMESPACE::success();
            }
        }
        else {
            size_t const n = size_t{b} - 0x80;
            if (n == 0) {
                out = T{};
                enc.remove_prefix(1);
                return BOOST_OUTCOME_V2_NAMESPACE::success();
            }
            unsigned char const *const p = enc.data() + 1;
            if (MONAD_LIKELY(
                    n <= sizeof(T) && n < enc.size() && p[0] != 0 &&
                    (n != 1 || p[0] >= 0x80))) {
                T v{};
                std::memcpy(&as_bytes(v)[sizeof(T) - n], p, n);
                out = bswap(v);
                enc.remove_prefix(1 + n);
                return BOOST_OUTCOME_V2_NAMESPACE::success();
            }
        }
    }
    BOOST_OUTCOME_TRY(out, decode_unsigned<T>(enc));
    return BOOST_OUTCOME_V2_NAMESPACE::success();
}
#endif

inline Result<bool> decode_bool(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto const i, decode_unsigned<uint64_t>(enc));

    if (MONAD_UNLIKELY(i > 1)) {
        return DecodeError::Overflow;
    }

    return i;
}

MONAD_RLP_NAMESPACE_END
