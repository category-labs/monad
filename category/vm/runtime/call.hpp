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
#include <category/vm/evm/delegation.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/types.hpp>

namespace monad::vm::runtime
{
    std::uint32_t message_flags(
        std::uint32_t env_flags, bool static_call, bool delegation_indicator);

    template <Traits traits>
    uint256_t call_impl(
        Context *ctx, uint256_t const &gas_word, uint256_t const &address,
        bool has_value, evmc_bytes32 const &value,
        uint256_t const &args_offset_word, uint256_t const &args_size_word,
        uint256_t const &ret_offset_word, uint256_t const &ret_size_word,
        evmc_call_kind call_kind, bool static_call,
        std::int64_t remaining_block_base_gas);

    template <Traits traits>
    void call(
        Context *ctx, uint256_t *result_ptr, uint256_t const *gas_ptr,
        uint256_t const *address_ptr, uint256_t const *value_ptr,
        uint256_t const *args_offset_ptr, uint256_t const *args_size_ptr,
        uint256_t const *ret_offset_ptr, uint256_t const *ret_size_ptr,
        std::int64_t remaining_block_base_gas);

    template <Traits traits>
    void callcode(
        Context *ctx, uint256_t *result_ptr, uint256_t const *gas_ptr,
        uint256_t const *address_ptr, uint256_t const *value_ptr,
        uint256_t const *args_offset_ptr, uint256_t const *args_size_ptr,
        uint256_t const *ret_offset_ptr, uint256_t const *ret_size_ptr,
        std::int64_t remaining_block_base_gas);

    template <Traits traits>
    void delegatecall(
        Context *ctx, uint256_t *result_ptr, uint256_t const *gas_ptr,
        uint256_t const *address_ptr, uint256_t const *args_offset_ptr,
        uint256_t const *args_size_ptr, uint256_t const *ret_offset_ptr,
        uint256_t const *ret_size_ptr, std::int64_t remaining_block_base_gas);

    template <Traits traits>
    void staticcall(
        Context *ctx, uint256_t *result_ptr, uint256_t const *gas_ptr,
        uint256_t const *address_ptr, uint256_t const *args_offset_ptr,
        uint256_t const *args_size_ptr, uint256_t const *ret_offset_ptr,
        uint256_t const *ret_size_ptr, std::int64_t remaining_block_base_gas);
}
