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

#include <category/crypto/keccak.h>
#include <category/crypto/keccak_batch.h>
#include <category/crypto/keccak_batch_impl.hpp>

#include <cstddef>

extern "C" void monad_keccak256_batch_avx2(
    monad_keccak256_job const *const jobs, size_t const count)
{
    size_t i = 0;
    for (; i + 4 <= count; i += 4) {
        keccak256_lanes<u64x4>(jobs + i);
    }
    size_t const rest = count - i;
    if (rest == 1) {
        monad_keccak256(jobs[i].in, jobs[i].len, jobs[i].out);
    }
    else if (rest > 1) {
        keccak256_partial<u64x4>(jobs + i, rest);
    }
}
