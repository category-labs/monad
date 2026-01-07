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

#include <category/vm/core/assert.h>

#include <immintrin.h>

#include <cstdint>

namespace monad::vm::runtime
{
    inline void non_temporal_bzero(void *dest, std::size_t n)
    {
        MONAD_VM_ASSERT((reinterpret_cast<uintptr_t>(dest) & 31) == 0);
        MONAD_VM_ASSERT((n & 31) == 0);
        auto *d = static_cast<std::uint8_t *>(dest);
        auto *const e = d + n;
        __m256i const zero = _mm256_setzero_si256();
        while (d < e) {
            _mm256_stream_si256(reinterpret_cast<__m256i *>(d), zero);
            d += 32;
        }
    }

    inline void non_temporal_memcpy(void *dest, void *src, std::size_t n)
    {
        MONAD_VM_ASSERT((reinterpret_cast<uintptr_t>(dest) & 31) == 0);
        MONAD_VM_ASSERT((reinterpret_cast<uintptr_t>(src) & 31) == 0);
        MONAD_VM_ASSERT((n & 31) == 0);
        auto *d = static_cast<std::uint8_t *>(dest);
        auto *s = static_cast<std::uint8_t *>(src);
        auto *const e = d + n;
        while (d < e) {
            _mm256_stream_si256(
                reinterpret_cast<__m256i *>(d),
                *reinterpret_cast<__m256i *>(s));
            d += 32;
            s += 32;
        }
    }
}
