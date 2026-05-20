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

#include <stdint.h>

/// Vocabulary type for C APIs that work with opaque 32 byte values; 32 bytes
/// (256 bits) is the native word size of the Ethereum virtual machine, and
/// typically represents either (1) a digest of the keccak hash function, or
/// (2) a signed or unsigned 256-bit big endian integer
typedef struct monad_bytes32
{
    uint8_t bytes[32];
} monad_bytes32;

/// A type alias which indicates that a 32 byte array should be understood to
/// have the uint256 big endian representation
typedef monad_bytes32 monad_uint256_be;

constexpr monad_bytes32 MONAD_BYTES32_ZERO = {};

[[gnu::always_inline]] static inline int
monad_bytes32_cmp(monad_bytes32 const *lhs, monad_bytes32 const *rhs)
{
    return __builtin_memcmp(lhs, rhs, sizeof *lhs);
}

[[gnu::always_inline]] static inline bool
monad_bytes32_eq(monad_bytes32 const *lhs, monad_bytes32 const *rhs)
{
    return monad_bytes32_cmp(lhs, rhs) == 0;
}
