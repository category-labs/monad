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

// zkVM mirror of category/core/immutable/set.hpp — see [[map.hpp]].

#pragma once

#include <ankerl/unordered_dense.h>

#include <cstddef>
#include <functional>
#include <utility>

namespace immutable
{
    template <class K, class Hash = std::hash<K>>
    class set
    {
        ankerl::unordered_dense::set<K, Hash> s_;

    public:
        set() = default;

        std::size_t count(K const &k) const
        {
            return s_.count(k);
        }

        set insert(K k) const
        {
            set result = *this;
            result.s_.insert(std::move(k));
            return result;
        }

        bool empty() const
        {
            return s_.empty();
        }

        auto begin() const
        {
            return s_.begin();
        }

        auto end() const
        {
            return s_.end();
        }
    };
}
