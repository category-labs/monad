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

#include <cstddef>

namespace monad::vm::compiler::poly_typed
{
    constexpr size_t max_kind_depth = 50;

    constexpr size_t max_kind_ticks = 10000;

    struct InferException
    {
    };

    struct DepthException : public InferException
    {
    };

    struct TickException : public InferException
    {
    };

    struct UnificationException : public InferException
    {
    };

    inline void increment_kind_depth(size_t &depth, size_t x)
    {
        depth += x;
        if (depth > max_kind_depth) {
            throw DepthException{};
        }
    }

    inline void increment_kind_ticks(size_t &ticks, size_t x)
    {
        ticks += x;
        if (ticks > max_kind_ticks) {
            throw TickException{};
        }
    }
}
