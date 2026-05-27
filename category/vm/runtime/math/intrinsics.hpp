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

// Platform-specific `mul` for the runtime math interface. The host build
// links the hand-rolled x86 assembly via the extern declarations below.

#pragma once

#include <category/core/runtime/uint256.hpp>

// It is assumed that if the `result` pointer overlaps with `left` and/or
// `right`, then `result` pointer is equal to `left` and/or `right`.
extern "C" void monad_vm_runtime_mul(
    monad::uint256_t *result, monad::uint256_t const *left,
    monad::uint256_t const *right) noexcept;

// It is assumed that if the `result` pointer overlaps with `left` and/or
// `right`, then `result` pointer is equal to `left` and/or `right`.
extern "C" void monad_vm_runtime_mul_192(
    monad::uint256_t *result, monad::uint256_t const *left,
    monad::uint256_t const *right) noexcept;

namespace monad::vm::runtime
{
    constexpr void (*mul)(
        uint256_t *, uint256_t const *,
        uint256_t const *) noexcept = monad_vm_runtime_mul;
}
