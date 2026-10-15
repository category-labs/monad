// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <bit>
#include <concepts>
#include <cstdint>

namespace monad::bit
{
#if defined(MONAD_ZKVM_AIRBENDER)
    // Airbender implements Zbb's rev8 alone (riscv_common::byte_swap), so the
    // guest is not built with Zbb and names the instruction locally.
    [[nodiscard, gnu::always_inline]] inline uint32_t
    airbender_rev8(uint32_t const x) noexcept
    {
        uint32_t r;
        __asm__(".option push\n\t"
                ".option arch, +zbb\n\t"
                "rev8 %0, %1\n\t"
                ".option pop"
                : "=r"(r)
                : "r"(x));
        return r;
    }
#endif

    template <std::integral T>
    [[nodiscard, gnu::always_inline]] inline constexpr T
    byteswap(T const x) noexcept
    {
#if defined(MONAD_ZKVM_AIRBENDER)
        if !consteval {
            if constexpr (sizeof(T) == 8) {
                auto const v = static_cast<uint64_t>(x);
                return static_cast<T>(
                    (uint64_t{airbender_rev8(static_cast<uint32_t>(v))} << 32) |
                    airbender_rev8(static_cast<uint32_t>(v >> 32)));
            }
            else if constexpr (sizeof(T) == 4) {
                return static_cast<T>(
                    airbender_rev8(static_cast<uint32_t>(x)));
            }
        }
#endif
        if constexpr (sizeof(T) == 8) {
            auto v = static_cast<uint64_t>(x);
            v = ((v & 0x00FF00FF00FF00FFull) << 8) |
                ((v >> 8) & 0x00FF00FF00FF00FFull);
            v = ((v & 0x0000FFFF0000FFFFull) << 16) |
                ((v >> 16) & 0x0000FFFF0000FFFFull);
            return static_cast<T>((v << 32) | (v >> 32));
        }
        else if constexpr (sizeof(T) == 4) {
            auto v = static_cast<uint32_t>(x);
            v = ((v & 0x00FF00FFu) << 8) | ((v >> 8) & 0x00FF00FFu);
            return static_cast<T>((v << 16) | (v >> 16));
        }
        else {
            return std::byteswap(x);
        }
    }

    // Smoke-test the two open-coded cases against the generic one.
    static_assert(byteswap(uint64_t{0x0123456789ABCDEF}) == 0xEFCDAB8967452301);
    static_assert(byteswap(uint32_t{0x01234567}) == 0x67452301);
    static_assert(byteswap(uint16_t{0x0123}) == 0x2301);
}
