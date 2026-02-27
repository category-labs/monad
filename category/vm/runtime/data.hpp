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

#include <category/vm/core/assert.h>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/types.hpp>

#include <cstdint>

namespace monad::vm::runtime
{
    template <Traits traits>
    void
    balance(Context *ctx, uint256_t *result_ptr, uint256_t const *address_ptr);

    inline void
    calldataload(Context *ctx, uint256_t *result_ptr, uint256_t const *i_ptr)
    {
        if (MONAD_VM_UNLIKELY(!is_bounded_by_bits<32>(*i_ptr))) {
            *result_ptr = 0;
            return;
        }

        auto const i{static_cast<std::uint32_t>(*i_ptr)};
        auto const n = int64_t{ctx->env.input_data_size} - int64_t{i};
        if (MONAD_VM_UNLIKELY(n <= 0)) {
            // Prevent undefined behavior from pointer arithmetic out of bounds.
            *result_ptr = 0;
            return;
        }

        *result_ptr = uint256_load_bounded_be(ctx->env.input_data + i, n);
    }

    template <Traits traits>
    void calldatacopy(
        Context *ctx, uint256_t const *dest_offset_ptr,
        uint256_t const *offset_ptr, uint256_t const *size_ptr);

    template <Traits traits>
    void codecopy(
        Context *ctx, uint256_t const *dest_offset_ptr,
        uint256_t const *offset_ptr, uint256_t const *size_ptr);

    template <Traits traits>
    void extcodecopy(
        Context *ctx, uint256_t const *address_ptr,
        uint256_t const *dest_offset_ptr, uint256_t const *offset_ptr,
        uint256_t const *size_ptr);

    template <Traits traits>
    void returndatacopy(
        Context *ctx, uint256_t const *dest_offset_ptr,
        uint256_t const *offset_ptr, uint256_t const *size_ptr);

    template <Traits traits>
    void extcodehash(
        Context *ctx, uint256_t *result_ptr, uint256_t const *address_ptr);

    template <Traits traits>
    void extcodesize(
        Context *ctx, uint256_t *result_ptr, uint256_t const *address_ptr);
}
