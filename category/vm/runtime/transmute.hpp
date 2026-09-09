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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/vm/runtime/transmute/intrinsics.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

namespace monad::vm::runtime
{
    static_assert(sizeof(evmc_address) == 20);
    static_assert(sizeof(bytes32_t) == 32);
    static_assert(sizeof(uint256_t) == 32);

    [[gnu::always_inline]]
    inline uint256_t
    uint256_load_bounded_be(uint8_t const *const bytes, int64_t const max_len)
    {
        return bswap(uint256_load_bounded_le(bytes, max_len));
    }

    [[gnu::always_inline]]
    inline Address address_from_uint256(uint256_t const &x)
    {
        auto const *bytes = as_bytes(x);

        uint64_t t2;
        std::memcpy(&t2, bytes, 8);
        t2 = std::byteswap(t2);

        uint64_t t1;
        std::memcpy(&t1, bytes + 8, 8);
        t1 = std::byteswap(t1);

        uint32_t t0;
        std::memcpy(&t0, bytes + 16, 4);
        t0 = std::byteswap(t0);

        Address ret;
        std::memcpy(ret.bytes, &t0, 4);
        std::memcpy(ret.bytes + 4, &t1, 8);
        std::memcpy(ret.bytes + 12, &t2, 8);
        return ret;
    }

    [[gnu::always_inline]]
    inline uint256_t uint256_from_address(Address const &addr)
    {
        uint32_t t2;
        std::memcpy(&t2, addr.bytes, 4);
        t2 = std::byteswap(t2);

        uint64_t t1;
        std::memcpy(&t1, addr.bytes + 4, 8);
        t1 = std::byteswap(t1);

        uint64_t t0;
        std::memcpy(&t0, addr.bytes + 12, 8);
        t0 = std::byteswap(t0);

        alignas(uint256_t) uint8_t ret[32];
        std::memcpy(ret, &t0, 8);
        std::memcpy(ret + 8, &t1, 8);
        std::memcpy(ret + 16, &t2, 4);
        std::memset(ret + 20, 0, 12);
        return std::bit_cast<uint256_t>(ret);
    }

    template <uint64_t N>
        requires(N < 64)
    [[gnu::always_inline]]
    constexpr bool is_bounded_by_bits(uint256_t const &x)
    {
        // `x[0] >> N` and `x[0] & ~((1 << N) - 1)` are zero on exactly the
        // same words, and the shift needs no constant. At N = 28 the mask has
        // 36 set bits, so it costs a `lui` of its own on every call --
        // 155,338 of them on block 25815042, 124,231 from MSTORE and MLOAD --
        // and the `and` that consumes it can never be a ZisK FROP, because
        // one operand is the mask. A shift by an immediate is one
        // instruction and folds into the or-reduction.
        return ((x[0] >> N) | x[1] | x[2] | x[3]) == 0;
    }

    template <typename T>
    [[gnu::always_inline]]
    constexpr T clamp_cast(uint256_t const &x) noexcept
    {
        return is_bounded_by_bits<std::numeric_limits<T>::digits>(x)
                   ? static_cast<T>(x)
                   : std::numeric_limits<T>::max();
    }
}
