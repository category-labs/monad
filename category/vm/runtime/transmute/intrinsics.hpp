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

// Host (AVX2) implementation of the runtime transmute primitive
// uint256_load_bounded_le, backed by hand-rolled x86 assembly in
// transmute.S.

#pragma once

#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/core/runtime/uint256.hpp>

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
    [[gnu::always_inline]]
    inline uint256_t
    uint256_load_bounded_le(uint8_t const *const bytes, int64_t const max_len)
    {
        if (MONAD_LIKELY(max_len >= 32)) {
            return load_le_unsafe<uint256_t>(bytes);
        }
        return uint256_t{monad_vm_runtime_load_bounded_le(bytes, max_len)};
    }
}
