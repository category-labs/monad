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

#include <cstddef>

MONAD_NAMESPACE_BEGIN

//! \brief A STL compatible hash based on the high quality FNV1 hash
//! algorithm
template <class T>
struct fnv1a_hash
{
    using working_type = uint64_t;

    static constexpr working_type begin() noexcept
    {
        return 14695981039346656037ULL;
    }

    static constexpr void add(working_type &hash, T v) noexcept
    {
        static constexpr working_type prime = 1099511628211ULL;
        unsigned char const *const _v =
            reinterpret_cast<unsigned char const *>(&v);
        // NOLINTNEXTLINE(bugprone-sizeof-expression)
        for (size_t n = 0; n < sizeof(T); n++) {
            hash ^= static_cast<working_type>(_v[n]);
            hash *= prime;
        }
    }

    constexpr size_t operator()(T v) const noexcept
    {
        auto ret = begin();
        add(ret, v);
        return ret;
    }
};

MONAD_NAMESPACE_END
