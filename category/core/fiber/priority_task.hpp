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

#include <cstdint>
#include <functional>

MONAD_FIBER_NAMESPACE_BEGIN

struct PriorityTask
{
    uint64_t priority{0};
    std::function<void()> task{};
};

static_assert(sizeof(PriorityTask) == 40);
static_assert(alignof(PriorityTask) == 8);

MONAD_FIBER_NAMESPACE_END
