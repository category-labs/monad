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

#ifndef ZKVM_ALLOCATOR_H
#define ZKVM_ALLOCATOR_H

#ifdef MONAD_ZKVM

    #include <stddef.h>

    #ifdef __cplusplus
extern "C"
{
    #endif

    #if defined(MONAD_ZKVM_ZISK)
void *sys_alloc_aligned(size_t bytes, size_t align);
    #elif defined(MONAD_ZKVM_SP1)
void *sp1_alloc_aligned(size_t bytes, size_t align);
    #endif

// Matches std::aligned_alloc(alignment, size) argument order.
inline void *zkvm_aligned_alloc(size_t alignment, size_t size)
{
    #if defined(MONAD_ZKVM_ZISK)
    return sys_alloc_aligned(size, alignment);
    #elif defined(MONAD_ZKVM_SP1)
    return sp1_alloc_aligned(size, alignment);
    #else
        #error                                                                 \
            "No zkVM aligned_alloc backend defined (expected MONAD_ZKVM_ZISK or MONAD_ZKVM_SP1)"
    #endif
}

    #ifdef __cplusplus
}
    #endif

#endif // MONAD_ZKVM

#endif // ZKVM_ALLOCATOR_H
