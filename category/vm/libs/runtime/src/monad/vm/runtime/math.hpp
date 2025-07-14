#pragma once

#include <monad/vm/core/assert.h>
#include <monad/vm/runtime/types.hpp>
#include <monad/vm/runtime/uint256.hpp>

#include <evmc/evmc.hpp>

// It is assumed that if the `result` pointer overlaps with `left` and/or
// `right`, then `result` pointer is equal to `left` and/or `right`.
extern "C" void monad_vm_runtime_mul_192(
    monad::vm::runtime::uint256_t *result,
    monad::vm::runtime::uint256_t const *left,
    monad::vm::runtime::uint256_t const *right) noexcept;

namespace monad::vm::runtime
{
    constexpr void (*mul)(
        uint256_t *, uint256_t const *,
        uint256_t const *) noexcept = monad_vm_runtime_mul;

    constexpr void udiv(
        uint256_t *result_ptr, uint256_t const *a_ptr,
        uint256_t const *b_ptr) noexcept
    {
        if (*b_ptr == 0) {
            *result_ptr = 0;
            return;
        }

        *result_ptr = *a_ptr / *b_ptr;
    }

    constexpr void sdiv(
        uint256_t *result_ptr, uint256_t const *a_ptr,
        uint256_t const *b_ptr) noexcept
    {
        if (*b_ptr == 0) {
            *result_ptr = 0;
            return;
        }

        *result_ptr = sdivrem(*a_ptr, *b_ptr).quot;
    }

    constexpr void umod(
        uint256_t *result_ptr, uint256_t const *a_ptr,
        uint256_t const *b_ptr) noexcept
    {
        if (*b_ptr == 0) {
            *result_ptr = 0;
            return;
        }

        *result_ptr = *a_ptr % *b_ptr;
    }

    constexpr void smod(
        uint256_t *result_ptr, uint256_t const *a_ptr,
        uint256_t const *b_ptr) noexcept
    {
        if (*b_ptr == 0) {
            *result_ptr = 0;
            return;
        }

        *result_ptr = sdivrem(*a_ptr, *b_ptr).rem;
    }

    constexpr void addmod(
        uint256_t *result_ptr, uint256_t const *a_ptr, uint256_t const *b_ptr,
        uint256_t const *n_ptr) noexcept
    {
        if (*n_ptr == 0) {
            *result_ptr = 0;
            return;
        }

        *result_ptr = addmod(*a_ptr, *b_ptr, *n_ptr);
    }

    constexpr void mulmod(
        uint256_t *result_ptr, uint256_t const *a_ptr, uint256_t const *b_ptr,
        uint256_t const *n_ptr) noexcept
    {
        if (*n_ptr == 0) {
            *result_ptr = 0;
            return;
        }

        *result_ptr = mulmod(*a_ptr, *b_ptr, *n_ptr);
    }

    template <evmc_revision Rev>
    constexpr void
    exp(Context *ctx, uint256_t *result_ptr, uint256_t const *a_ptr,
        uint256_t const *exponent_ptr) noexcept
    {
        auto exponent_byte_size = count_significant_bytes(*exponent_ptr);

        auto exponent_cost = [] -> decltype(exponent_byte_size) {
            if constexpr (Rev >= EVMC_SPURIOUS_DRAGON) {
                return 50;
            }
            else {
                return 10;
            }
        }();

        ctx->deduct_gas(exponent_byte_size * exponent_cost);

        *result_ptr = exp(*a_ptr, *exponent_ptr);
    }
}
