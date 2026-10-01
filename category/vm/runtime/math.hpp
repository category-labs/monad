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

#include <category/core/assert.h>
#include <category/core/runtime/uint256.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/math/intrinsics.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.hpp>

namespace monad::vm::runtime
{
    constexpr void udiv(
        uint256_t *const result_ptr, uint256_t const *const a_ptr,
        uint256_t const *const b_ptr) noexcept
    {
        if (*b_ptr == 0) {
            *result_ptr = 0;
            return;
        }

        *result_ptr = *a_ptr / *b_ptr;
    }

    constexpr void sdiv(
        uint256_t *const result_ptr, uint256_t const *const a_ptr,
        uint256_t const *const b_ptr) noexcept
    {
        if (*b_ptr == 0) {
            *result_ptr = 0;
            return;
        }

        *result_ptr = sdivrem(*a_ptr, *b_ptr).quot;
    }

    constexpr void umod(
        uint256_t *const result_ptr, uint256_t const *const a_ptr,
        uint256_t const *const b_ptr) noexcept
    {
        if (*b_ptr == 0) {
            *result_ptr = 0;
            return;
        }

        *result_ptr = *a_ptr % *b_ptr;
    }

    constexpr void smod(
        uint256_t *const result_ptr, uint256_t const *const a_ptr,
        uint256_t const *const b_ptr) noexcept
    {
        if (*b_ptr == 0) {
            *result_ptr = 0;
            return;
        }

        *result_ptr = sdivrem(*a_ptr, *b_ptr).rem;
    }

    constexpr void addmod(
        uint256_t *const result_ptr, uint256_t const *const a_ptr,
        uint256_t const *const b_ptr, uint256_t const *const n_ptr) noexcept
    {
        if (*n_ptr == 0) {
            *result_ptr = 0;
            return;
        }
#ifdef MONAD_ZKVM_ZISK
        // Write (a * 1 + b) % n directly into the result slot.
        if !consteval {
            zisk_arith256_mod_to(
                reinterpret_cast<uint64_t *>(result_ptr),
                reinterpret_cast<uint64_t const *>(a_ptr),
                zisk_one_limbs,
                reinterpret_cast<uint64_t const *>(b_ptr),
                reinterpret_cast<uint64_t const *>(n_ptr));
            return;
        }
#endif

        *result_ptr = addmod(*a_ptr, *b_ptr, *n_ptr);
    }

    constexpr void mulmod(
        uint256_t *const result_ptr, uint256_t const *const a_ptr,
        uint256_t const *const b_ptr, uint256_t const *const n_ptr) noexcept
    {
        if (*n_ptr == 0) {
            *result_ptr = 0;
            return;
        }
#ifdef MONAD_ZKVM_ZISK
        // Write (a * b + 0) % n directly into the result slot.
        if !consteval {
            zisk_arith256_mod_to(
                reinterpret_cast<uint64_t *>(result_ptr),
                reinterpret_cast<uint64_t const *>(a_ptr),
                reinterpret_cast<uint64_t const *>(b_ptr),
                zisk_zero_limbs,
                reinterpret_cast<uint64_t const *>(n_ptr));
            return;
        }
#endif

        *result_ptr = mulmod(*a_ptr, *b_ptr, *n_ptr);
    }

    template <Traits traits>
    [[gnu::always_inline]]
    constexpr uint32_t exp_dynamic_gas_cost_multiplier() noexcept
    {
        static_assert(traits::evm_rev() >= MONAD_ETH_SPURIOUS_DRAGON);
        return 50;
    }

    template <Traits traits>
    constexpr void
    exp(Context *ctx, uint256_t *result_ptr, uint256_t const *a_ptr,
        uint256_t const *exponent_ptr) noexcept
    {
        auto const exponent_byte_size = count_significant_bytes(*exponent_ptr);

        auto const exponent_cost = exp_dynamic_gas_cost_multiplier<traits>();

        ctx->deduct_gas(exponent_byte_size * exponent_cost);

        *result_ptr = exp(*a_ptr, *exponent_ptr);
    }
}
