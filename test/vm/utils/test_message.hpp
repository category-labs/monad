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

#include <test/vm/utils/test_memory.hpp>

#include <evmc/evmc.h>

namespace monad::vm::test
{
    struct TestMessage
    {
        TestMemory test_memory;
        evmc_message msg;

        TestMessage()
            : msg{}
        {
            msg.memory_handle = test_memory.data;
            msg.memory = test_memory.data;
            msg.memory_capacity = test_memory.capacity;
        }

        evmc_message &operator*()
        {
            return msg;
        }

        evmc_message *operator->()
        {
            return &msg;
        }
    };
}
