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

#include <evmc/evmc.hpp>

#include <algorithm>
#include <cstddef>
#include <functional>

MONAD_NAMESPACE_BEGIN

using Address = ::evmc::address;

static_assert(sizeof(Address) == 20);
static_assert(alignof(Address) == 1);

constexpr bool is_zero(evmc_address const &addr)
{
    return std::ranges::all_of(addr.bytes, [](auto const b) { return b == 0; });
}

MONAD_NAMESPACE_END

namespace boost
{
    inline size_t hash_value(monad::Address const &address) noexcept
    {
        return std::hash<monad::Address>{}(address);
    }
}
