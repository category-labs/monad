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

#include <category/vm/runtime/types.hpp>

#include <test/vm/utils/test_memory.hpp>

#include <functional>

namespace monad::vm::test
{
    struct TestContext
    {
        TestMemory test_memory;
        runtime::Context ctx;

        using Builder = std::function<void(runtime::Context &)>;

        TestContext(Builder build = [](auto &) {})
            : ctx{runtime::Context::empty(
                  test_memory.data, test_memory.capacity)}
        {
            build(ctx);
        }

        runtime::Context &operator*()
        {
            return ctx;
        }

        runtime::Context *operator->()
        {
            return &ctx;
        }
    };
}
