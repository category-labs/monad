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

#pragma once

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_keccak256_job
{
    uint8_t const *in;
    size_t len;
    uint8_t *out; // 32 bytes; may alias this job's input, but no other job's
};

// Keccak-256 of independent messages, hashed 4 or 8 at a time in SIMD lanes.
// Jobs are grouped in array order and a group costs as many permutations as
// its longest message, so callers with mixed lengths should sort by length.
void monad_keccak256_batch(
    struct monad_keccak256_job const *jobs, size_t count);

// The kernels monad_keccak256_batch() picks between at runtime. The avx512
// one requires AVX-512F and AVX-512VL.
void monad_keccak256_batch_avx2(
    struct monad_keccak256_job const *jobs, size_t count);
void monad_keccak256_batch_avx512(
    struct monad_keccak256_job const *jobs, size_t count);

#ifdef __cplusplus
}
#endif
