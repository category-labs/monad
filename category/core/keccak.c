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

#include <category/core/keccak.h>

#include <stddef.h>
#include <stdint.h>

#define BLOCK_SIZE ((1600 - 2 * 256) / 8)

extern size_t
SHA3_absorb(uint64_t A[5][5], unsigned char const *inp, size_t len, size_t r);

extern void
SHA3_squeeze(uint64_t A[5][5], unsigned char *out, size_t len, size_t r);

void keccak256(
    unsigned char const *const in, unsigned long const len,
    unsigned char out[KECCAK256_SIZE])
{
    uint64_t A[5][5];
    unsigned char blk[BLOCK_SIZE];

    __builtin_memset(A, 0, sizeof(A));

    size_t const rem = SHA3_absorb(A, in, len, BLOCK_SIZE);
    if (rem > 0) {
        __builtin_memcpy(blk, &in[len - rem], rem);
    }
    __builtin_memset(&blk[rem], 0, BLOCK_SIZE - rem);
    blk[rem] = 0x01;
    blk[BLOCK_SIZE - 1] |= 0x80;
    (void)SHA3_absorb(A, blk, BLOCK_SIZE, BLOCK_SIZE);

    SHA3_squeeze(A, out, 32, BLOCK_SIZE);
}
