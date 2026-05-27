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

#include <category/core/runtime/uint256/portable.hpp>
#include <category/core/runtime/uint256/types.hpp>

#include <cstddef>
#include <cstdint>

// zkVM (RISC-V) replacement for the AVX2/BMI2 x86 intrinsics. RISC-V has no
// specialised instructions (mulx, shld, shrd, div, addc/subb) corresponding
// to the x86 backend, so we re-export the portable implementations as the
// intrinsics implementations.

namespace monad::uint256::intrinsics
{
    using portable::addc;
    using portable::div;
    using portable::mulx;
    using portable::shld;
    using portable::shrd;
    using portable::subb;
    using portable::truncating_mul;

    [[gnu::always_inline]] constexpr inline uint64_t
    force(uint64_t const expr) noexcept
    {
        return expr;
    }
}
