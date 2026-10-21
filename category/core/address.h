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

/// Vocabulary type for C APIs that work with Ethereum account addresses
typedef struct monad_address
{
    uint8_t bytes[20];
} monad_address;

constexpr monad_address MONAD_ADDRESS_ZERO = {};

/// Compare two addresses, as if by memcmp(3)
[[gnu::always_inline]] static inline int monad_address_cmp(
    monad_address const *const lhs, monad_address const *const rhs)
{
    return __builtin_memcmp(lhs, rhs, sizeof *lhs);
}

/// Returns true if two addresses are equal
[[gnu::always_inline]] static inline bool
monad_address_eq(monad_address const *const lhs, monad_address const *const rhs)
{
    return monad_address_cmp(lhs, rhs) == 0;
}

#ifdef __cplusplus
} // extern "C"
#endif
