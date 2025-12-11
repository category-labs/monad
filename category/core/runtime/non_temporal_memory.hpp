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
        MONAD_VM_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(dest) & 31) == 0);
        MONAD_VM_DEBUG_ASSERT((n & 31) == 0);
        auto *s = reinterpret_cast<__m256i *>(dest);
        auto *const t = reinterpret_cast<std::uint8_t *>(dest);
        auto *const e = reinterpret_cast<__m256i *>(t + n);
        __m256i const zero = _mm256_set_epi64x(0, 0, 0, 0);
        while (s < e) {
            _mm256_stream_si256(s, zero);
            ++s;
        }
    }

    inline void non_temporal_memcpy(void *dest, void *src, std::size_t n)
    {
        MONAD_VM_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(dest) & 31) == 0);
        MONAD_VM_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(src) & 31) == 0);
        MONAD_VM_DEBUG_ASSERT((n & 31) == 0);
        auto *d = reinterpret_cast<__m256i *>(dest);
        auto *s = reinterpret_cast<__m256i *>(src);
        auto *const t = reinterpret_cast<std::uint8_t *>(dest);
        auto *const e = reinterpret_cast<__m256i *>(t + n);
        while (d < e) {
            _mm256_stream_si256(d, *s);
            ++d;
            ++s;
        }
    }
}
