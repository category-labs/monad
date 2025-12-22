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

#include <category/core/assert.h>

#include <cstdint>

namespace monad::vm::runtime
{
    class VmMemory
    {
        std::uint8_t *memory_;
        std::uint32_t capacity_;

    public:
        VmMemory();
        explicit VmMemory(std::uint32_t memory_capacity);

        VmMemory(VmMemory &&);
        VmMemory &operator=(VmMemory &&);

        ~VmMemory();

        std::uint32_t capacity() const
        {
            return capacity_;
        }

        std::uint8_t *memory()
        {
            return memory_;
        }
    };
}
