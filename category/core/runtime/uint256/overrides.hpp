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

// Guest shadow headers can enable backend overrides. Host operators retain
// their existing code, so discarded override calls need declarations only.
namespace monad::uint256::overrides
{
    inline constexpr bool enabled = false;

    template <typename U>
    constexpr bool is_nonzero(U const &) noexcept;
    template <typename U>
    constexpr bool less(U const &, U const &) noexcept;
    template <typename U>
    constexpr bool equal(U const &, U const &) noexcept;
}
