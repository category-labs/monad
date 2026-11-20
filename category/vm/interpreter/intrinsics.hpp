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

#include <cstddef>
#include <cstdint>
#include <utility>

// Host reads of interpreter bits and bytes. Guest builds override them through
// their shadow header.

// Bit I % 64 of WORD.
#define MONAD_VM_TEST_BIT(WORD, I) (((WORD) >> ((I) & 63)) & 1)

namespace monad::vm::interpreter
{
    namespace detail
    {
        // Assemble K big-endian bytes directly to avoid a temporary and a
        // software byte swap on targets without a byte-swap instruction.
        template <size_t K>
        [[gnu::always_inline]] inline uint64_t
        load_be_k(uint8_t const *const p) noexcept
        {
            static_assert(K >= 1 && K <= 8);
            return [p]<size_t... Is>(std::index_sequence<Is...>) {
                return (
                    (static_cast<uint64_t>(p[Is]) << (8 * (K - 1 - Is))) | ...);
            }(std::make_index_sequence<K>{});
        }
    }
}
