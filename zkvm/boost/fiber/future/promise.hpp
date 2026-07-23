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

// zkVM shadow of <boost/fiber/future/promise.hpp>.
//
// The guest executes transactions sequentially with no fibers, so the
// cross-fiber completion handshake in execute_transaction / execute_block —
// a promise the speculative-execution fiber fulfils, awaited before the next
// transaction merges — has nothing to wait on. Replace boost.fiber's promise
// and future with no-op stand-ins exposing only the surface the guest
// compiles against: every get_future / wait / get / set_value returns
// immediately. Production code links unchanged without dragging boost.fiber
// (its scheduler, <thread>, TBB) into the bare-metal guest.

#pragma once

#include <type_traits>

namespace boost::fibers
{
    template <class T>
    class future
    {
    public:
        void wait() const noexcept {}

        decltype(auto) get() noexcept
        {
            if constexpr (!std::is_void_v<T>) {
                return T{};
            }
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
