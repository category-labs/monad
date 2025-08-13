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

#pragma once

#include <category/core/config.hpp>

#include <bit>
#include <cstdint>

MONAD_NAMESPACE_BEGIN

class Incarnation
{
    uint64_t block_ : 40;
    uint64_t tx_ : 24;

public:
    static constexpr uint64_t LAST_TX = (1UL << 24) - 1;

    explicit Incarnation(uint64_t const block, uint64_t const tx)
        : block_{block & 0xFFFFFFFFFF}
        , tx_{tx & 0xFFFFFF}
    {
    }

    uint64_t get_block() const
    {
        return block_;
    }

    uint64_t get_tx() const
    {
        return tx_;
    }

    uint64_t to_int() const
    {
        return std::bit_cast<uint64_t>(*this);
    }

    static Incarnation from_int(uint64_t const incarnation)
    {
        return std::bit_cast<Incarnation>(incarnation);
    }
};

static_assert(sizeof(Incarnation) == 8);

inline bool operator==(Incarnation const i1, Incarnation const i2)
{
    return i1.to_int() == i2.to_int();
}

MONAD_NAMESPACE_END
