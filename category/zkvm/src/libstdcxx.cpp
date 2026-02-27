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

// Minimal C++ runtime stubs for bare-metal zkVM.
#ifdef MONAD_ZKVM

    #include <category/zkvm/zkvm_allocator.h>
    #include <category/zkvm/zkvm_exit.h>

    #include <cstddef>

// operator new / delete
[[gnu::always_inline]] static inline void *alloc_or_exit(std::size_t size)
{
    if (size == 0) {
        zkvm_exit(1);
    }
    void *ptr = zkvm_aligned_alloc(16, size);
    if (!ptr) {
        zkvm_exit(1);
    }
    return ptr;
}

void *operator new(std::size_t size)
{
    return alloc_or_exit(size);
}

void *operator new[](std::size_t size)
{
    return alloc_or_exit(size);
}

void operator delete(void *) noexcept {}

void operator delete[](void *) noexcept {}

void operator delete(void *, std::size_t) noexcept {}

void operator delete[](void *, std::size_t) noexcept {}

namespace std
{
    [[noreturn]] void terminate() noexcept
    {
        zkvm_exit(1);
    }
}

#endif
