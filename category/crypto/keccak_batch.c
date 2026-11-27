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

#include <category/crypto/keccak_batch.h>

#include <stddef.h>

void monad_keccak256_batch(
    struct monad_keccak256_job const *const jobs, size_t const count)
{
    if (__builtin_cpu_supports("avx512f") &&
        __builtin_cpu_supports("avx512vl")) {
        monad_keccak256_batch_avx512(jobs, count);
    }
    else {
        monad_keccak256_batch_avx2(jobs, count);
    }
}
