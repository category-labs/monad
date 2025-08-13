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

#include <category/core/fiber/config.hpp>

#include <boost/fiber/context.hpp>
#include <boost/fiber/properties.hpp>

#include <cstdint>

MONAD_FIBER_NAMESPACE_BEGIN

using boost::fibers::context;
using boost::fibers::fiber_properties;

class PriorityProperties final : public fiber_properties
{
    uint64_t priority_ = 0;

public:
    explicit PriorityProperties(context *const ctx) noexcept
        : fiber_properties{ctx}
    {
    }

    [[gnu::always_inline]] uint64_t get_priority() const noexcept
    {
        return priority_;
    }

    [[gnu::always_inline]] void set_priority(uint64_t const priority) noexcept
    {
        priority_ = priority;

        notify();
    }
};

MONAD_FIBER_NAMESPACE_END
