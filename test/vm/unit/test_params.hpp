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

namespace monad::vm::compiler::test
{
    struct TestParams
    {
    public:
        bool dump_asm_on_failure = false;

        TestParams(bool dump_asm_on_failure = false)
            : dump_asm_on_failure(dump_asm_on_failure)
        {
        }
    };

    // We could use testing::AddGlobalTestEnvironment(new TestParams(...))
    // instead of using a global variable like google suggests, but that's
    // overkill for our usage, where we simply want to pass a flag to the tests.
    extern struct TestParams params;
}
