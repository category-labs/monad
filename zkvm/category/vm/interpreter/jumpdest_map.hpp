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

#if !defined(MONAD_ZKVM_ZISK)
    #include_next <category/vm/interpreter/jumpdest_map.hpp>
#else
    #include <category/vm/interpreter/intrinsics.hpp>

    #include <algorithm>
    #include <cstddef>
    #include <cstdint>

namespace monad::vm::interpreter
{
    // One bit per code byte. Explicit 64-bit words define the layout for
    // precompile access, unlike std::vector<bool>'s opaque storage.
    class JumpdestMap
    {
        // Cover every PUSH2 destination (2^16 bits). This relies on fresh,
        // zero-filled ZisK bump memory: allocations are never reused, and
        // analysis leaves every bit beyond the code unset.
        static constexpr size_t min_words = (size_t{1} << 16) / 64;
        uint64_t *words_{nullptr};
        size_t word_count_{0};

    public:
        // is_jumpdest16 needs no bounds check: PUSH2 destinations fit.
        static constexpr bool covers_push2 = true;

        JumpdestMap() = default;

        explicit JumpdestMap(size_t const bits)
            : words_{static_cast<uint64_t *>(::operator new(
                  std::max((bits + 63) / 64, min_words) * sizeof(uint64_t)))}
            , word_count_{std::max((bits + 63) / 64, min_words)}
        {
        }

        void set(size_t const i) noexcept
        {
            // Set bit i % 64 in word i / 64.
            words_[i >> 6] |= uint64_t{1} << (i & 63);
        }

        // Let FrameCode test the same bitmap without owning the map.
        [[gnu::always_inline]] static bool
        test(uint64_t const *const words, size_t const i) noexcept
        {
            return MONAD_VM_TEST_BIT(words[i >> 6], i);
        }

        bool test(size_t const i) const noexcept
        {
            return test(words_, i);
        }

        size_t word_count() const noexcept
        {
            return word_count_;
        }

        uint64_t *words() noexcept
        {
            return words_;
        }

        uint64_t const *words() const noexcept
        {
            return words_;
        }
    };
}
#endif
