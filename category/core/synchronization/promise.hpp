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

#include <category/core/config.hpp>

#include <boost/fiber/future/promise.hpp>

MONAD_NAMESPACE_BEGIN

// This is a zero-cost synchronization abstraction over a reference to a
// boost::fibers::promise<void>. It is used to coordinate between strands of
// transaction execution. The point of this thin abstraction is to allow it to
// be shadowed on a platform that does not have boost::fibers, without having to
// change the code that uses it.
class Promise
{
    boost::fibers::promise<void> &promise_;

public:
    explicit Promise(boost::fibers::promise<void> &promise) noexcept
        : promise_{promise}
    {
    }

    void wait() const
    {
        promise_.get_future().wait();
    }
};

static_assert(
    sizeof(Promise) == sizeof(void *), "Promise should have no overhead");

MONAD_NAMESPACE_END
