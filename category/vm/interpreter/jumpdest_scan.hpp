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

#include <cstdint>
#include <span>

namespace monad::vm::interpreter
{
    // Return true after filling map; false requests the portable scan.
    // Guest builds override this hook through their shadow header.
    template <typename JumpdestMap>
    [[gnu::always_inline]] inline bool accelerated_find_jumpdests(
        std::span<uint8_t const> /*code*/, JumpdestMap & /*map*/)
    {
        return false;
    }
}
