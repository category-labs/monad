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

#include <category/core/fiber/priority_pool.hpp>

#include <category/core/fiber/config.hpp>
#include <category/core/fiber/fiber_group.hpp>
#include <category/core/fiber/fiber_thread_pool.hpp>

#include <memory>

MONAD_FIBER_NAMESPACE_BEGIN

PriorityPool::PriorityPool(
    unsigned const n_threads, unsigned const n_fibers, bool const prevent_spin)
    : thread_pool_{std::make_unique<FiberThreadPool>(n_threads, prevent_spin)}
    , fiber_group_{thread_pool_->create_fiber_group(n_fibers)}
{
}

MONAD_FIBER_NAMESPACE_END
