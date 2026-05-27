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

// zkVM fallback for uint256_load_bounded_le: memcpy-based, no AVX
// intrinsics and no asm dependency.

#pragma once

#include <category/core/runtime/uint256.hpp>

#include <algorithm>
#include <cstring>

namespace monad::vm::runtime
{
    [[gnu::always_inline]]
    inline uint256_t
    uint256_load_bounded_le(uint8_t const *const bytes, int64_t const max_len)
    {
        uint256_t v{0};
        if (max_len <= 0) {
            return v;
        }
        std::memcpy(
            as_bytes(v),
            bytes,
            std::min(max_len, static_cast<int64_t>(uint256_t::num_bytes)));
        return v;
    }
}
