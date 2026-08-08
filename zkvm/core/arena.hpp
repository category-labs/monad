// Copyright (C) 2026 Category Labs, Inc.
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

#include <cstddef>

// Shared bump arena for buffers the guest never frees.
// Keep both pointers together so accesses share one base address.
struct ZkvmArena
{
    unsigned char *next;
    unsigned char *end;
};

extern "C" ZkvmArena zkvm_arena;

// Handle zero-byte requests and refill exhausted chunks out of line.
[[gnu::noinline, gnu::cold]] void *zkvm_arena_alloc_slow(std::size_t size);

[[gnu::always_inline]] inline void *zkvm_arena_alloc(std::size_t const size)
{
    unsigned char *const next = zkvm_arena.next;
    // Remaining space is a multiple of 16, so test the fit before rounding.
    // size - 1 also sends zero-byte requests to the slow path.
    if (size - 1 >= static_cast<std::size_t>(zkvm_arena.end - next)) {
        return zkvm_arena_alloc_slow(size);
    }
    // Round up to a multiple of 16 to keep subsequent allocations aligned.
    // size fits what is left here, so the addition cannot wrap.
    zkvm_arena.next = next + ((size + 15) & ~std::size_t{15});
    return next;
}
