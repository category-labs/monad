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

#include <category/vm/interpreter/intrinsics.hpp>

#include <cstddef>
#include <cstdint>
#include <vector>

namespace monad::vm::interpreter
{
    // One bit per code byte. Explicit 64-bit words define the layout for
    // precompile access, unlike std::vector<bool>'s opaque storage. Guest
    // builds override this map through their shadow header.
    class JumpdestMap
    {
        std::vector<uint64_t> words_;

    public:
        // is_jumpdest16 needs a bounds check: the map ends with the code.
        static constexpr bool covers_push2 = false;

        JumpdestMap() = default;

        explicit JumpdestMap(size_t const bits)
            : words_((bits + 63) / 64, 0)
        {
        }

        void set(size_t const i) noexcept
        {
            // Set bit i % 64 in word i / 64.
            words_[i >> 6] |= uint64_t{1} << (i & 63);
        }

        bool test(size_t const i) const noexcept
        {
            // Read bit i % 64 from word i / 64.
            return MONAD_VM_TEST_BIT(words_[i >> 6], i);
        }

        size_t word_count() const noexcept
        {
            return words_.size();
        }

        uint64_t *words() noexcept
        {
            return words_.data();
        }
    };
}
