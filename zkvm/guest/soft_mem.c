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

// EXPERIMENT, measurement only: memcpy, memmove, memset and memcmp in
// software, the guest's only definitions: ziskos built with its no-dma-mem
// feature leaves them undefined, so the C++ and the Rust code alike call
// these. A run that issues no DMA operation plans none of the four DMA
// instances. Compiled with -fno-builtin -fno-tree-loop-distribute-patterns so
// GCC does not turn a loop back into a call to the function it implements.
//
// Main's steps are what these cost: one a RISC-V instruction, about five a
// byte for a byte loop. So they move 8 bytes an instruction wherever they can,
// at any alignment: ZisK proves a misaligned access in its MemAlign instance
// for one Main step. Most copies of a block (two thirds of the bytes at 50 tx)
// do not share their source's alignment, and most are short (half under 32
// bytes), so neither a word loop that needs both ends aligned nor head and
// tail bytes copied one by one would leave much of the gain.

#include <stddef.h>
#include <stdint.h>

// 8- and 4-byte accesses at any alignment. Inline assembly: GCC, which assumes
// a misaligned access is slow on RISC-V, would split them into bytes.
static inline uint64_t load64(void const *const p)
{
    uint64_t v;
    __asm__("ld %0, 0(%1)"
            : "=r"(v)
            : "r"(p), "m"(*(unsigned char const(*)[8])p));
    return v;
}

static inline void store64(void *const p, uint64_t const v)
{
    __asm__("sd %1, 0(%2)"
            : "=m"(*(unsigned char(*)[8])p)
            : "r"(v), "r"(p));
}

static inline uint32_t load32(void const *const p)
{
    uint32_t v;
    __asm__("lwu %0, 0(%1)"
            : "=r"(v)
            : "r"(p), "m"(*(unsigned char const(*)[4])p));
    return v;
}

static inline void store32(void *const p, uint32_t const v)
{
    __asm__("sw %1, 0(%2)"
            : "=m"(*(unsigned char(*)[4])p)
            : "r"(v), "r"(p));
}

// Forward from the first byte on, every 8-byte block loaded before it is
// stored: memmove's copy when the destination overlaps the source from below,
// where the stores stay below the next loads. Destination aligned word by
// word, the head and tail bytes one by one.
static void copy_forward(unsigned char *d, unsigned char const *s, size_t n)
{
    if (n >= 16) {
        while ((uintptr_t)d & 7u) {
            *d++ = *s++;
            --n;
        }
        uint64_t *dw = (uint64_t *)d;
        for (; n >= 8; n -= 8, s += 8) {
            *dw++ = load64(s);
        }
        d = (unsigned char *)dw;
    }
    while (n--) {
        *d++ = *s++;
    }
}

// Head and tail as one misaligned word each, which overlap the words between
// them: correct because memcpy's ends do not overlap, which is also why
// memmove does not call it when they do.
void *memcpy(void *const dst, void const *const src, size_t n)
{
    unsigned char *d = (unsigned char *)dst;
    unsigned char const *s = (unsigned char const *)src;
    if (n < 8) {
        if (n >= 4) {
            store32(d, load32(s));
            store32(d + n - 4, load32(s + n - 4));
        }
        else {
            while (n--) {
                *d++ = *s++;
            }
        }
        return dst;
    }
    unsigned char *const end = d + n;
    unsigned char const *const send = s + n;
    store64(d, load64(s));
    size_t const head = 8 - ((uintptr_t)d & 7u);
    d += head;
    s += head;
    n -= head;
    uint64_t *dw = (uint64_t *)d;
    for (; n >= 32; n -= 32, s += 32, dw += 4) {
        uint64_t const a = load64(s);
        uint64_t const b = load64(s + 8);
        uint64_t const c = load64(s + 16);
        uint64_t const e = load64(s + 24);
        dw[0] = a;
        dw[1] = b;
        dw[2] = c;
        dw[3] = e;
    }
    for (; n >= 8; n -= 8, s += 8) {
        *dw++ = load64(s);
    }
    if (n) {
        store64(end - 8, load64(send - 8));
    }
    return dst;
}

void *memmove(void *const dst, void const *const src, size_t n)
{
    unsigned char *d = (unsigned char *)dst;
    unsigned char const *s = (unsigned char const *)src;
    if (d == s || n == 0) {
        return dst;
    }
    if (d + n <= s || d >= s + n) {
        return memcpy(dst, src, n);
    }
    if (d < s) {
        copy_forward(d, s, n);
        return dst;
    }
    // Overlapping, destination above: backwards, the mirror of copy_forward.
    d += n;
    s += n;
    if (n >= 16) {
        while ((uintptr_t)d & 7u) {
            *--d = *--s;
            --n;
        }
        uint64_t *dw = (uint64_t *)d;
        for (; n >= 8; n -= 8) {
            s -= 8;
            *--dw = load64(s);
        }
        d = (unsigned char *)dw;
    }
    while (n--) {
        *--d = *--s;
    }
    return dst;
}

void *memset(void *const dst, int const c, size_t n)
{
    unsigned char *d = (unsigned char *)dst;
    unsigned char const b = (unsigned char)c;
    uint64_t const w = 0x0101010101010101ull * b;
    if (n < 8) {
        if (n >= 4) {
            store32(d, (uint32_t)w);
            store32(d + n - 4, (uint32_t)w);
        }
        else {
            while (n--) {
                *d++ = b;
            }
        }
        return dst;
    }
    unsigned char *const end = d + n;
    store64(d, w);
    size_t const head = 8 - ((uintptr_t)d & 7u);
    d += head;
    n -= head;
    uint64_t *dw = (uint64_t *)d;
    for (; n >= 32; n -= 32, dw += 4) {
        dw[0] = w;
        dw[1] = w;
        dw[2] = w;
        dw[3] = w;
    }
    for (; n >= 8; n -= 8) {
        *dw++ = w;
    }
    if (n) {
        store64(end - 8, w);
    }
    return dst;
}

// Word by word while the words are equal; the bytes of the first word that
// differs (or of the tail) decide.
int memcmp(void const *const a, void const *const b, size_t n)
{
    unsigned char const *x = (unsigned char const *)a;
    unsigned char const *y = (unsigned char const *)b;
    for (; n >= 8 && load64(x) == load64(y); n -= 8, x += 8, y += 8) {
    }
    for (; n; --n, ++x, ++y) {
        if (*x != *y) {
            return (int)*x - (int)*y;
        }
    }
    return 0;
}
