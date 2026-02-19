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

#include <category/core/assert.h>
#include <category/core/runtime/uint256.hpp>

#include <algorithm>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <limits>

namespace monad::vm::runtime
{

    uint256_t countr_zero(uint256_t const &x)
    {
        int total_count = 0;
        for (size_t i = 0; i < 4; i++) {
            int const count = std::countr_zero(x[i]);
            total_count += count;
            if (count < 64) {
                return uint256_t{total_count};
            }
        }
        return uint256_t{total_count};
    }

    uint256_t
    from_bytes(std::size_t n, std::size_t remaining, uint8_t const *src)
    {
        MONAD_ASSERT(n <= 32);

        if (n == 0) {
            return 0;
        }

        uint8_t dst[32] = {};

        std::memcpy(&dst[32 - n], src, std::min(n, remaining));

        return uint256_t::load_be(dst);
    }

    uint256_t from_bytes(std::size_t const n, uint8_t const *src)
    {
        return from_bytes(n, n, src);
    }

}
