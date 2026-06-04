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

// zkVM mirror of category/core/immutable/map.hpp — drop-in replacement
// exposing only the API surface used by State / AccountState (find,
// insert, iteration). Backed by ankerl::unordered_dense::map.

#pragma once

#include <ankerl/unordered_dense.h>

#include <functional>
#include <utility>

namespace immutable
{
    template <class K, class V, class Hash = std::hash<K>>
    class map
    {
        ankerl::unordered_dense::map<K, V, Hash> m_;

    public:
        map() = default;

        V const *find(K const &k) const
        {
            auto const it = m_.find(k);
            return it == m_.end() ? nullptr : &it->second;
        }

        map insert(std::pair<K, V> p) const
        {
            map result = *this;
            result.m_.insert_or_assign(std::move(p.first), std::move(p.second));
            return result;
        }

        bool empty() const
        {
            return m_.empty();
        }

        auto begin() const
        {
            return m_.begin();
        }

        auto end() const
        {
            return m_.end();
        }
    };
}
