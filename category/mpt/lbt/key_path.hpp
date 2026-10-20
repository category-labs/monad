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

#include <category/core/assert.h>
#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <array>

MONAD_MPT_NAMESPACE_BEGIN

namespace lbt
{
    // The nibbles a StateMachine has been walked through, indexed by depth.
    // Only [0, depth) is meaningful: up() leaves stale nibbles at and beyond
    // depth.
    class KeyPath
    {
    public:
        // NibblesView holds at most 255 nibbles; an even capacity packs into
        // whole bytes.
        static constexpr unsigned CAPACITY = 254;

        void set(unsigned const depth, unsigned char const nibble) noexcept
        {
            MONAD_ASSERT(depth < CAPACITY && nibble < 16);
            auto &byte = bytes_[depth / 2];
            byte =
                depth % 2 == 0
                    ? static_cast<unsigned char>((byte & 0x0f) | (nibble << 4))
                    : static_cast<unsigned char>((byte & 0xf0) | nibble);
        }

        void set(unsigned const depth, NibblesView const nibbles) noexcept
        {
            MONAD_ASSERT(depth + nibbles.nibble_size() <= CAPACITY);
            for (unsigned i = 0; i < nibbles.nibble_size(); ++i) {
                set(depth + i, nibbles.get(i));
            }
        }

        NibblesView
        view(unsigned const begin, unsigned const end) const noexcept
        {
            MONAD_ASSERT(begin <= end && end <= CAPACITY);
            return NibblesView{begin, end, bytes_.data()};
        }

    private:
        std::array<unsigned char, CAPACITY / 2> bytes_{};
    };
}

MONAD_MPT_NAMESPACE_END
