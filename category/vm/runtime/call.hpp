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
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/types.hpp>

namespace monad::vm::runtime
{
    inline std::uint32_t message_flags(
        std::uint32_t env_flags, bool static_call, bool delegation_indicator)
    {
        if (static_call) {
            env_flags = static_cast<std::uint32_t>(EVMC_STATIC);
        }

        if (delegation_indicator) {
            env_flags |= static_cast<std::uint32_t>(EVMC_DELEGATED);
        }
        else {
            env_flags &= ~static_cast<std::uint32_t>(EVMC_DELEGATED);
        }

        return env_flags;
    }

    template <evmc_revision Rev>
    uint256_t call_impl(
        Context *ctx, uint256_t const &gas_word, uint256_t const &address,
        bool has_value, evmc_bytes32 const &value,
        uint256_t const &args_offset_word, uint256_t const &args_size_word,
        uint256_t const &ret_offset_word, uint256_t const &ret_size_word,
        evmc_call_kind call_kind, bool static_call,
        std::int64_t remaining_block_base_gas)
    {
        ctx->env.clear_return_data();

        auto args_size = ctx->get_memory_offset(args_size_word);
        auto args_offset = (*args_size > 0)
                               ? ctx->get_memory_offset(args_offset_word)
                               : bin<0>;

        auto ret_size = ctx->get_memory_offset(ret_size_word);
        auto ret_offset =
            (*ret_size > 0) ? ctx->get_memory_offset(ret_offset_word) : bin<0>;

        ctx->expand_memory(max(args_offset + args_size, ret_offset + ret_size));

        auto const dest_address = address_from_uint256(address);

        if constexpr (Rev >= EVMC_BERLIN) {
            auto access_status =
                ctx->host->access_account(ctx->context, &dest_address);
            if (access_status == EVMC_ACCESS_COLD) {
                ctx->gas_remaining -= 2500;
            }
        }

        auto const code_address = [&]() -> evmc::address {
            if constexpr (Rev >= EVMC_PRAGUE) {
                // EIP-7702: if the code address starts with 0xEF0100, then
                // treat it as a delegated call in the context of the
                // current authority.
                if (auto delegate_address = evm::resolve_delegation(
                        ctx->host, ctx->context, dest_address)) {
                    auto const access_status = ctx->host->access_account(
                        ctx->context, &*delegate_address);
                    ctx->gas_remaining -=
                        access_status == EVMC_ACCESS_COLD ? 2600 : 100;
                    return *delegate_address;
                }
            }
            return dest_address;
        }();

        auto recipient = (call_kind == EVMC_CALL || static_call)
                             ? dest_address
                             : ctx->env.recipient;

        auto sender = (call_kind == EVMC_DELEGATECALL) ? ctx->env.sender
                                                       : ctx->env.recipient;

        if (has_value) {
            ctx->gas_remaining -= 9000;
        }

        if (call_kind == EVMC_CALL) {
            if (MONAD_VM_UNLIKELY(
                    has_value && (ctx->env.evmc_flags & EVMC_STATIC))) {
                auto error_code =
                    ctx->gas_remaining + remaining_block_base_gas < 0
                        ? StatusCode::OutOfGas
                        : StatusCode::Error;
                ctx->exit(error_code);
            }

            auto has_empty_cost = true;
            if constexpr (Rev >= EVMC_SPURIOUS_DRAGON) {
                has_empty_cost = has_value;
            }
            if (has_empty_cost &&
                !ctx->host->account_exists(ctx->context, &dest_address)) {
                ctx->gas_remaining -= 25000;
            }
        }

        auto gas_left_here = ctx->gas_remaining + remaining_block_base_gas;

        if (MONAD_VM_UNLIKELY(gas_left_here < 0)) {
            ctx->exit(StatusCode::OutOfGas);
        }

        auto gas = clamp_cast<std::int64_t>(gas_word);

        if constexpr (Rev >= EVMC_TANGERINE_WHISTLE) {
            gas = std::min(gas, gas_left_here - (gas_left_here / 64));
        }
        else {
            if (MONAD_VM_UNLIKELY(gas > gas_left_here)) {
                ctx->exit(StatusCode::OutOfGas);
            }
        }

        if (has_value) {
            gas += 2300;
            ctx->gas_remaining += 2300;
        }

        if (MONAD_VM_UNLIKELY(ctx->env.depth >= 1024)) {
            return 0;
        }

        auto message = evmc_message{
            .kind = call_kind,
            .flags = message_flags(
                ctx->env.evmc_flags, static_call, dest_address != code_address),
            .depth = ctx->env.depth + 1,
            .gas = gas,
            .recipient = recipient,
            .sender = sender,
            .input_data =
                (*args_size > 0) ? ctx->memory.data + *args_offset : nullptr,
            .input_size = *args_size,
            .value = value,
            .create2_salt = ctx->env.create2_salt,
            .code_address = code_address,
            .code = nullptr,
            .code_size = 0,
        };

        auto result = ctx->host->call(ctx->context, &message);

        ctx->deduct_gas(gas - result.gas_left);
        ctx->gas_refund += result.gas_refund;
        ctx->env.set_return_data(result.output_data, result.output_size);

        auto copy_size =
            std::min(static_cast<std::size_t>(*ret_size), result.output_size);
        std::copy_n(
            result.output_data, copy_size, ctx->memory.data + *ret_offset);

        return (result.status_code == EVMC_SUCCESS) ? 1 : 0;
    }

    template <evmc_revision Rev>
    void call(
        Context *ctx, uint256_t *result_ptr, uint256_t const *gas_ptr,
        uint256_t const *address_ptr, uint256_t const *value_ptr,
        uint256_t const *args_offset_ptr, uint256_t const *args_size_ptr,
        uint256_t const *ret_offset_ptr, uint256_t const *ret_size_ptr,
        std::int64_t remaining_block_base_gas)
    {
        *result_ptr = call_impl<Rev>(
            ctx,
            *gas_ptr,
            *address_ptr,
            *value_ptr != 0,
            bytes32_from_uint256(*value_ptr),
            *args_offset_ptr,
            *args_size_ptr,
            *ret_offset_ptr,
            *ret_size_ptr,
            EVMC_CALL,
            false,
            remaining_block_base_gas);
    }

    template <evmc_revision Rev>
    void callcode(
        Context *ctx, uint256_t *result_ptr, uint256_t const *gas_ptr,
        uint256_t const *address_ptr, uint256_t const *value_ptr,
        uint256_t const *args_offset_ptr, uint256_t const *args_size_ptr,
        uint256_t const *ret_offset_ptr, uint256_t const *ret_size_ptr,
        std::int64_t remaining_block_base_gas)
    {
        *result_ptr = call_impl<Rev>(
            ctx,
            *gas_ptr,
            *address_ptr,
            *value_ptr != 0,
            bytes32_from_uint256(*value_ptr),
            *args_offset_ptr,
            *args_size_ptr,
            *ret_offset_ptr,
            *ret_size_ptr,
            EVMC_CALLCODE,
            false,
            remaining_block_base_gas);
    }

    template <evmc_revision Rev>
    void delegatecall(
        Context *ctx, uint256_t *result_ptr, uint256_t const *gas_ptr,
        uint256_t const *address_ptr, uint256_t const *args_offset_ptr,
        uint256_t const *args_size_ptr, uint256_t const *ret_offset_ptr,
        uint256_t const *ret_size_ptr, std::int64_t remaining_block_base_gas)
    {
        *result_ptr = call_impl<Rev>(
            ctx,
            *gas_ptr,
            *address_ptr,
            false,
            ctx->env.value,
            *args_offset_ptr,
            *args_size_ptr,
            *ret_offset_ptr,
            *ret_size_ptr,
            EVMC_DELEGATECALL,
            false,
            remaining_block_base_gas);
    }

    template <evmc_revision Rev>
    void staticcall(
        Context *ctx, uint256_t *result_ptr, uint256_t const *gas_ptr,
        uint256_t const *address_ptr, uint256_t const *args_offset_ptr,
        uint256_t const *args_size_ptr, uint256_t const *ret_offset_ptr,
        uint256_t const *ret_size_ptr, std::int64_t remaining_block_base_gas)
    {
        MONAD_VM_DEBUG_ASSERT(Rev >= EVMC_BYZANTIUM);
        *result_ptr = call_impl<Rev>(
            ctx,
            *gas_ptr,
            *address_ptr,
            false,
            evmc::bytes32{},
            *args_offset_ptr,
            *args_size_ptr,
            *ret_offset_ptr,
            *ret_size_ptr,
            EVMC_CALL,
            true,
            remaining_block_base_gas);
    }
}
