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

#include <boost/context/fiber.hpp>

namespace boost::context::detail
{
    // Missing from libboost_context, which is built for fcontext.
    // NOLINTNEXTLINE(bugprone-exception-escape)
    fiber_activation_record *&fiber_activation_record::current() noexcept
    {
        thread_local fiber_activation_record main_record;
        thread_local fiber_activation_record *active = &main_record;
        return active;
    }
}
