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
// software, reached through the linker's --wrap so that no call lands on
// ziskos' DMA versions. A run that issues no DMA operation plans none of the
// four DMA instances. Word-wise when both ends share an alignment, byte-wise
// otherwise; compiled with -fno-builtin -fno-tree-loop-distribute-patterns so
// GCC does not turn a loop back into a call to the function it implements.

#include <stddef.h>
#include <stdint.h>

void *__wrap_memcpy(void *dst, void const *src, size_t n)
{
    unsigned char *d = (unsigned char *)dst;
    unsigned char const *s = (unsigned char const *)src;
    if ((((uintptr_t)d ^ (uintptr_t)s) & 7u) == 0) {
        while (n && ((uintptr_t)d & 7u)) {
            *d++ = *s++;
            --n;
        }
        uint64_t *dw = (uint64_t *)d;
        uint64_t const *sw = (uint64_t const *)s;
        for (; n >= 8; n -= 8) {
            *dw++ = *sw++;
        }
        d = (unsigned char *)dw;
        s = (unsigned char const *)sw;
    }
    while (n--) {
        *d++ = *s++;
    }
    return dst;
}

void *__wrap_memmove(void *dst, void const *src, size_t n)
{
    unsigned char *d = (unsigned char *)dst;
    unsigned char const *s = (unsigned char const *)src;
    if (d == s || n == 0) {
        return dst;
    }
    if (d < s || d >= s + n) {
        return __wrap_memcpy(dst, src, n);
    }
    // Overlapping, destination above: copy backwards.
    d += n;
    s += n;
    while (n--) {
        *--d = *--s;
    }
    return dst;
}

void *__wrap_memset(void *dst, int c, size_t n)
{
    unsigned char *d = (unsigned char *)dst;
    unsigned char const b = (unsigned char)c;
    while (n && ((uintptr_t)d & 7u)) {
        *d++ = b;
        --n;
    }
    uint64_t const w = 0x0101010101010101ull * b;
    uint64_t *dw = (uint64_t *)d;
    for (; n >= 8; n -= 8) {
        *dw++ = w;
    }
    d = (unsigned char *)dw;
    while (n--) {
        *d++ = b;
    }
    return dst;
}

int __wrap_memcmp(void const *a, void const *b, size_t n)
{
    unsigned char const *x = (unsigned char const *)a;
    unsigned char const *y = (unsigned char const *)b;
    for (; n; --n, ++x, ++y) {
        if (*x != *y) {
            return (int)*x - (int)*y;
        }
    }
    return 0;
}
