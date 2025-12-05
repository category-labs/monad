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

#include <category/core/runtime/uint256.hpp>
#include <category/vm/core/assert.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <immintrin.h>

// Load `load_size` bytes from `src_buffer` and clear the remaining upper bytes
// of the result. It is required that `load_size <= 32`. If `load_size <= 0`
// then zero is returned.
extern "C" __m256i
monad_vm_runtime_load_bounded_le(uint8_t const *src_buffer, int64_t load_size);

// Note: monad_vm_runtime_load_bounded_le_raw uses non-standard
// calling convention. See transmute.S. Use the
// monad_vm_runtime_load_bounded_le function for a version
// using standard calling convention.
extern "C" __m256i monad_vm_runtime_load_bounded_le_raw();

namespace monad::vm::runtime
{
    static_assert(sizeof(evmc_address) == 20);
    static_assert(sizeof(evmc_bytes32) == 32);
    static_assert(sizeof(uint256_t) == 32);

    [[gnu::always_inline]]
    inline uint256_t
    uint256_load_bounded_le(std::uint8_t const *bytes, std::int64_t max_len)
    {
        if (MONAD_VM_LIKELY(max_len >= 32)) {
            return uint256_t::load_le_unsafe(bytes);
        }
        return uint256_t{monad_vm_runtime_load_bounded_le(bytes, max_len)};
    }

    [[gnu::always_inline]]
    inline uint256_t
    uint256_load_bounded_be(std::uint8_t const *bytes, std::int64_t max_len)
    {
        return uint256_load_bounded_le(bytes, max_len).to_be();
    }

    [[gnu::always_inline]]
    inline evmc::bytes32 bytes32_from_uint256(uint256_t const &x)
    {
        evmc_bytes32 ret;
        x.store_be(ret.bytes);
        return ret;
    }

    [[gnu::always_inline]]
    inline evmc::address address_from_uint256(uint256_t const &x)
    {
        auto const *bytes = x.as_bytes();

        std::uint64_t t2;
        std::memcpy(&t2, bytes, 8);
        t2 = std::byteswap(t2);

        std::uint64_t t1;
        std::memcpy(&t1, bytes + 8, 8);
        t1 = std::byteswap(t1);

        std::uint32_t t0;
        std::memcpy(&t0, bytes + 16, 4);
        t0 = std::byteswap(t0);

        evmc_address ret;
        std::memcpy(ret.bytes, &t0, 4);
        std::memcpy(ret.bytes + 4, &t1, 8);
        std::memcpy(ret.bytes + 12, &t2, 8);
        return ret;
    }

    [[gnu::always_inline]]
    inline uint256_t uint256_from_bytes32(evmc::bytes32 const &x)
    {
        return uint256_t::load_be(x.bytes);
    }

    [[gnu::always_inline]]
    inline uint256_t uint256_from_address(evmc::address const &addr)
    {
        std::uint32_t t2;
        std::memcpy(&t2, addr.bytes, 4);
        t2 = std::byteswap(t2);

        std::uint64_t t1;
        std::memcpy(&t1, addr.bytes + 4, 8);
        t1 = std::byteswap(t1);

        std::uint64_t t0;
        std::memcpy(&t0, addr.bytes + 12, 8);
        t0 = std::byteswap(t0);

        alignas(uint256_t) uint8_t ret[32];
        std::memcpy(ret, &t0, 8);
        std::memcpy(ret + 8, &t1, 8);
        std::memcpy(ret + 16, &t2, 4);
        std::memset(ret + 20, 0, 12);
        return std::bit_cast<uint256_t>(ret);
    }

    template <std::uint64_t N>
        requires(N < 64)
    [[gnu::always_inline]]
    constexpr bool is_bounded_by_bits(uint256_t const &x)
    {
        static constexpr std::uint64_t mask = ~((std::uint64_t{1} << N) - 1);
        return ((x[0] & mask) | x[1] | x[2] | x[3]) == 0;
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
