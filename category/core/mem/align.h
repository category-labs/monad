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

#pragma once

/**
 * @file
 *
 * Utilities for manually aligning sizes and addresses
 */

#include <stdbit.h>
#include <stddef.h>

#include <category/core/assert.h>

[[gnu::always_inline]] static inline size_t
monad_round_size_to_align(size_t const size, size_t const align)
{
    MONAD_ASSERT(stdc_has_single_bit(align));
    return (size + align - 1) & ~(align - 1);
}
