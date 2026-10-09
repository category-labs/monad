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

#include <category/core/config.hpp>

// Workarounds for what the guest's compiler emits, where the fix is a property
// of the generated code rather than of the algorithm.

MONAD_NAMESPACE_BEGIN

// Avoid ZisK's byte-store surcharge for nonzero upper register bits.
// Keep the value full-width through an asm barrier before narrowing it.
// Pass v in [0, 255]; the barrier does not clear its upper bits.
// The barrier is ZisK-only and skipped during constant evaluation.
[[gnu::always_inline]] constexpr unsigned char zx(unsigned long v) noexcept
{
#if defined(MONAD_ZKVM_ZISK)
    if !consteval {
        asm("" : "+r"(v));
    }
#endif
    return static_cast<unsigned char>(v);
}

MONAD_NAMESPACE_END
