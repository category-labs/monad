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

#include <type_traits>

namespace monad::vm::utils
{
    template <typename X, typename... Xs, typename Y, typename... Ys>
    consteval bool same_signature(X (*)(Xs...), Y (*)(Ys...)) noexcept
    {
        return std::is_same_v<X, Y> && (std::is_same_v<Xs, Ys> && ...);
    }
}
