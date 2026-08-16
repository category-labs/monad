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
//
// Also carries one libgcc override — see __popcountdi2 at the bottom.

#include <category/core/bit_primitives.hpp>
#include <zkvm/core/libc.hpp>

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
    return sys_alloc_aligned(size, 16);
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

void *aligned_alloc(std::size_t alignment, std::size_t size)
{
    if (alignment == 0 || (alignment & (alignment - 1)) != 0) {
        return nullptr;
    }
    if (size % alignment != 0) {
        return nullptr;
    }
    return sys_alloc_aligned(size, alignment);
}

// riscv64ima has no `cpop`, so every __builtin_popcountll becomes a call to
// libgcc's helper. immer's HAMT makes 41,909 of them per block (25551991) —
// 1,257,270 steps, 0.96 % of the guest — and libgcc's body is 30 instructions
// because it rebuilds each of the SWAR's four 64-bit constants from
// lui/addi/slli/add, which is what a 64-bit immediate costs on this target.
//
// bits::popcount64 is the same arithmetic with the constants fetched from
// .rodata: 19 instructions and four 8-aligned 8-byte loads. Against libgcc's
// 30 that is 684 COST per call, 28.7 M, 0.14 %.
//
// Defining the symbol here rather than patching a caller: libgcc is a static
// archive searched after this object, so the linker resolves __popcountdi2 to
// this definition and never pulls libgcc's _popcountdi2.o. That is the same
// mechanism malloc/free above rely on, and it composes with the immer hunk in
// third_party/patches — if that is ever applied, immer inlines its own copy
// and this simply goes uncalled.
//
// It is also the one change on this branch whose *effect* a build cannot show
// by passing: if the link order ever put libgcc first, this would silently do
// nothing. To check it took, disassemble __popcountdi2 in the ELF — 19
// instructions with two `ld` off a shared anchor is this one, 30 with three
// `lui` is libgcc's.
int __popcountdi2(std::uint64_t const x)
{
    return monad::bits::popcount64(x);
}

} // extern "C"
