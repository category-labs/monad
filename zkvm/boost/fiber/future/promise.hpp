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

#include <type_traits>

// The guest executes transactions sequentially with no fibers.
// Replace boost.fiber's promise and future with no-op stand-ins.

namespace boost::fibers
{
    template <class T>
    class future
    {
    public:
        void wait() const noexcept {}

        decltype(auto) get() noexcept
        {
            static_assert(std::is_void_v<T>);
        }
    };

    template <class T>
    class promise
    {
    public:
        promise() = default;

        future<T> get_future() noexcept
        {
            return {};
        }

        template <class... Args>
        void set_value(Args &&...) noexcept
        {
        }
    };
}
