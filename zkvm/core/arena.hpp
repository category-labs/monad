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

// The bump arena behind operator new (zkvm/core/libstdcxx.cpp). Nothing in the
// guest is ever freed, so a buffer that would be malloc'd can be bumped from
// here inline instead: no call, and no spills around one.

// The next free address and the chunk's end, side by side: one address formed
// on entry reaches both, where two separate variables took an address each for
// the loads and another for the store.
struct ZkvmArena
{
    unsigned char *cur;
    unsigned char *end;
};

extern "C" ZkvmArena zkvm_arena;

// Serves a request that does not fit what is left of the chunk, or a zero-byte
// one, starting a new chunk if needed. Out of line and cold: it holds the only
// calls and halts, so the inline fast path below stays free of them: a caller
// spills around it on that path only, and operator new tail-calls it.
[[gnu::noinline, gnu::cold]] void *zkvm_arena_alloc_slow(std::size_t size);

[[gnu::always_inline]] inline void *zkvm_arena_alloc(std::size_t const size)
{
    unsigned char *const cur = zkvm_arena.cur;
    // What is left is always a multiple of 16 -- every chunk is one, and every
    // request takes one from it -- so a request fits exactly when its size
    // rounded up to 16 does, and the size can be tested before it is rounded.
    // A zero-byte request wraps size - 1, so it takes the slow path too.
    if (size - 1 >= static_cast<std::size_t>(zkvm_arena.end - cur)) {
        return zkvm_arena_alloc_slow(size);
    }
    // Round up to a multiple of 16 to keep subsequent allocations aligned.
    // size fits what is left here, so the addition cannot wrap.
    zkvm_arena.cur = cur + ((size + 15) & ~std::size_t{15});
    return cur;
}
