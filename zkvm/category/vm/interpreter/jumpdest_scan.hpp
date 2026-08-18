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

// zkVM mirror: ZisK builds the JUMPDEST bitmap with its JUMPDEST precompile.
// Other zkVM backends keep the portable scan.

#pragma once

#include <cstddef>
#include <cstdint>
#include <span>

namespace monad::vm::interpreter
{
    template <typename JumpdestMap>
    [[gnu::always_inline]] inline bool accelerated_find_jumpdests(
        [[maybe_unused]] std::span<uint8_t const> const code,
        [[maybe_unused]] JumpdestMap &map)
    {
#ifdef MONAD_ZKVM_ZISK
        // Requires nonempty code, aligned buffers and whole-word capacity.
        // Buffers must be 8-byte aligned. Pass src via csrs, dst/size via add.
        auto const aligned =
            (reinterpret_cast<uintptr_t>(code.data()) % 8) == 0 &&
            (reinterpret_cast<uintptr_t>(map.words()) % 8) == 0;
        auto const covered = map.word_count() >= (code.size() + 63) / 64;
        if (aligned && covered && !code.empty()) {
            uint64_t *const dst = map.words();
            uint8_t const *const src = code.data();
            size_t const size = code.size();
            asm volatile("csrs 0x81c, %0\n\t"
                         "add x0, %1, %2\n\t"
                         :
                         : "r"(src), "r"(dst), "r"(size)
                         : "memory");
            return true;
        }
#endif
        return false;
    }
}
