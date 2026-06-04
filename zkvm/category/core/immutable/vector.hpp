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

// zkVM mirror of category/core/immutable/vector.hpp — see [[map.hpp]].

#pragma once

#include <cstddef>
#include <utility>
#include <vector>

namespace immutable
{
    template <class T>
    class vector
    {
        std::vector<T> v_;

    public:
        vector() = default;

        vector push_back(T x) const
        {
            vector result = *this;
            result.v_.push_back(std::move(x));
            return result;
        }

        auto begin() const
        {
            return v_.begin();
        }

        auto end() const
        {
            return v_.end();
        }

        std::size_t size() const
        {
            return v_.size();
        }

        bool empty() const
        {
            return v_.empty();
        }
    };
}
