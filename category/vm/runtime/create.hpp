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
#include <category/vm/evm/delegation.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.hpp>

namespace monad::vm::runtime
{
    consteval Bin<2> create_code_word_cost(evmc_revision rev)
    {
        return (rev >= EVMC_SHANGHAI) ? bin<2> : bin<0>;
    }

    consteval Bin<4> create2_code_word_cost(evmc_revision rev)
    {
        return (rev >= EVMC_SHANGHAI) ? bin<8> : bin<6>;
    }

    template <Traits traits>
    uint256_t create_impl(
        Context *ctx, uint256_t const &value, uint256_t const &offset_word,
        uint256_t const &size_word, uint256_t const &salt_word,
        evmc_call_kind kind, std::int64_t remaining_block_base_gas);

    template <Traits traits>
    void create(
        Context *ctx, uint256_t *result_ptr, uint256_t const *value_ptr,
        uint256_t const *offset_ptr, uint256_t const *size_ptr,
        std::int64_t remaining_block_base_gas);

    template <Traits traits>
    void create2(
        Context *ctx, uint256_t *result_ptr, uint256_t const *value_ptr,
        uint256_t const *offset_ptr, uint256_t const *size_ptr,
        uint256_t const *salt_ptr, std::int64_t remaining_block_base_gas);
}
