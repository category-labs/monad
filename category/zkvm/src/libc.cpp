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

// Minimal C library functions for bare-metal zkVM.
// The zkVM environment uses a bump allocator — free is a no-op.
#ifdef MONAD_ZKVM

    #include <category/zkvm/zkvm_allocator.h>

    #include <cstddef>
    #include <cstdint>
    #include <cstring>

extern "C"
{

void *malloc(std::size_t size)
{
    if (size == 0) {
        return nullptr;
    }
    return zkvm_aligned_alloc(16, size);
}

void free(void *ptr)
{
    // Bump allocator — no deallocation.
    (void)ptr;
}

void *calloc(std::size_t num, std::size_t size)
{
    std::size_t total;
    if (__builtin_mul_overflow(num, size, &total)) {
        return nullptr;
    }
    void *ptr = malloc(total);
    if (ptr) {
        std::memset(ptr, 0, total);
    }
    return ptr;
}

} // extern "C"

#endif
