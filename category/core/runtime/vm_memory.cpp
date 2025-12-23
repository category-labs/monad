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

#include <category/core/runtime/vm_memory.hpp>

#include <cstdlib>
#include <cstring>

namespace monad::vm::runtime
{
    VmMemory::VmMemory(std::uint32_t n)
        : capacity_{n}
    {
        MONAD_ASSERT((n & 31) == 0);

        void *const p = std::aligned_alloc(32, capacity_);
        MONAD_ASSERT(p != nullptr);

        std::memset(p, 0, n);
        memory_ = reinterpret_cast<std::uint8_t *>(p);
    }

    VmMemory::~VmMemory()
    {
        std::free(memory_);
    }
}
