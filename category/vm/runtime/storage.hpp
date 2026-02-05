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

#include <category/core/runtime/uint256.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/runtime/storage_costs.hpp>
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.hpp>

#include <array>

namespace monad::vm::runtime
{
    template <Traits traits>
    void sload(Context *ctx, uint256_t *result_ptr, uint256_t const *key_ptr);

    template <Traits traits>
    void sstore(
        Context *ctx, uint256_t const *key_ptr, uint256_t const *value_ptr,
        std::int64_t remaining_block_base_gas);

    void tload(Context *ctx, uint256_t *result_ptr, uint256_t const *key_ptr);

    void
    tstore(Context *ctx, uint256_t const *key_ptr, uint256_t const *val_ptr);

    bool debug_tstore_stack(
        Context const *ctx, uint256_t const *stack, uint64_t stack_size,
        uint64_t offset, uint64_t base_offset);
}
