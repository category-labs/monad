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

#include <bit>
#include <climits>
#include <cstdint>

#define MONAD_NAMESPACE_BEGIN                                                  \
    namespace monad                                                            \
    {

#define MONAD_NAMESPACE_END }

#define MONAD_NAMESPACE ::monad

#define MONAD_ANONYMOUS_NAMESPACE_BEGIN                                        \
    MONAD_NAMESPACE_BEGIN                                                      \
    namespace                                                                  \
    {

#define MONAD_ANONYMOUS_NAMESPACE_END                                          \
    }                                                                          \
    MONAD_NAMESPACE_END

// Asserts a sizeof/alignof/offsetof budget that only holds under the 64-bit
// host ABI. Pointer, size_t and container widths all shrink on a 32-bit target
// (the rv32im zkVM guest), moving every offset in a type that contains one, so
// these budgets are compiled out there rather than restated as a second set of
// magic numbers that nothing would keep honest. Layout properties that hold on
// every target — an alignment that comes from a uint64_t member, say — should
// stay a plain static_assert.
#if UINTPTR_MAX == UINT64_MAX
    #define MONAD_ASSERT_LP64_LAYOUT(...) static_assert(__VA_ARGS__)
#else
    #define MONAD_ASSERT_LP64_LAYOUT(...)
#endif

static_assert(CHAR_BIT == 8);

static_assert(
    std::endian::native == std::endian::big ||
    std::endian::native == std::endian::little);
