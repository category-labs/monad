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
#include <category/core/config.hpp>
#include <category/core/hex.hpp>

#include <category/execution/ethereum/precompiles.hpp>

#include <blst.h>

#include <array>
#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

namespace bls12
{
    // 48-byte type for the BLS12-381 field prime, satisfies the FixedBytes
    // concept so it can be initialised with from_hex.
    struct fp_bytes_t
    {
        uint8_t bytes[48];
    };

    // BLS12-381 field prime p per EIP-2537:
    // p =
    // 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
    inline constexpr fp_bytes_t BASE_FIELD_MODULUS =
        from_hex<fp_bytes_t>(
            "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f624"
            "1eabfffeb153ffffb9feffffffffaaab")
            .value();

    // 64-byte comparison buffer: 16 zero-padding bytes followed by the
    // 48-byte big-endian prime. Used by read_fp for the memcmp range check.
    inline constexpr std::array<uint8_t, 64> BASE_FIELD_MODULUS_BYTES = [] {
        std::array<uint8_t, 64> buf{};
        for (std::size_t i = 0; i < sizeof(BASE_FIELD_MODULUS.bytes); ++i) {
            buf[16 + i] = BASE_FIELD_MODULUS.bytes[i];
        }
        return buf;
    }();
    static_assert(BASE_FIELD_MODULUS_BYTES.size() == 64);

    template <typename Group>
    uint16_t msm_discount(uint64_t);

    struct G1
    {
        static constexpr auto element_encoded_size = 64;
        static constexpr auto encoded_size = 2 * element_encoded_size;
    };

    struct G2
    {
        static constexpr auto element_encoded_size =
            2 * G1::element_encoded_size;
        static constexpr auto encoded_size = 2 * element_encoded_size;
    };
} // namespace bls12

MONAD_NAMESPACE_END
