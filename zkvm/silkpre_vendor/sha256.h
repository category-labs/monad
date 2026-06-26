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

#include <category/core/assert.h>

#include <core/zkvm_accelerators.h>

#include <stddef.h>
#include <stdint.h>

#if defined(__cplusplus)
extern "C"
{
#endif

static inline void monad_sha256(
    uint8_t hash[32], uint8_t const *input, size_t len, bool use_cpu_extensions)
{
    (void)use_cpu_extensions;
    zkvm_status const status =
        zkvm_sha256(input, len, (zkvm_sha256_hash *)hash);
    MONAD_ASSERT(status == ZKVM_EOK);
}

#if defined(__cplusplus)
}
#endif
