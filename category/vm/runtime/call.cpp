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

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/core/runtime/uint256.hpp>
#include <category/vm/evm/delegation.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/revision.h>
#include <category/vm/evm/traits.hpp>
#if defined(MONAD_ZKVM_ZISK)
    #include <category/vm/host.hpp>
#endif
#include <category/vm/runtime/bin.hpp>
#include <category/vm/runtime/call.hpp>
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>

namespace monad::vm::runtime
{
    inline uint32_t message_flags(
        uint32_t env_flags, bool const static_call,
        bool const delegation_indicator)
    {
        if (static_call) {
            env_flags = static_cast<uint32_t>(EVMC_STATIC);
        }

        if (delegation_indicator) {
            env_flags |= static_cast<uint32_t>(EVMC_DELEGATED);
        }
        else {
            env_flags &= ~static_cast<uint32_t>(EVMC_DELEGATED);
        }

        return env_flags;
    }

#if defined(MONAD_ZKVM_ZISK)
    // Inlined into each caller: out of line, a call saves twelve registers,
    // passes five arguments on the stack and copies its result out of a
    // temporary, and the callers' constant call_kind, static_call and
    // has_value do not fold.
    #define MONAD_VM_CALL_IMPL_INLINE [[gnu::always_inline]] inline
#else
    #define MONAD_VM_CALL_IMPL_INLINE
#endif

    template <Traits traits>
    MONAD_VM_CALL_IMPL_INLINE uint256_t call_impl(
        Context *ctx, uint256_t const &gas_word, uint256_t const &address,
        bool const has_value, bytes32_t const &value,
        uint256_t const &args_offset_word, uint256_t const &args_size_word,
        uint256_t const &ret_offset_word, uint256_t const &ret_size_word,
        evmc_call_kind const call_kind, bool const static_call,
        int64_t const remaining_block_base_gas)
    {
        static_assert(traits::evm_rev() >= MONAD_ETH_BERLIN);

        ctx->env.clear_return_data();

        auto const args_size = ctx->get_memory_offset(args_size_word);
        auto const args_offset = (*args_size > 0)
                                     ? ctx->get_memory_offset(args_offset_word)
                                     : bin<0>;

        auto const ret_size = ctx->get_memory_offset(ret_size_word);
        auto const ret_offset =
            (*ret_size > 0) ? ctx->get_memory_offset(ret_offset_word) : bin<0>;

        ctx->expand_memory<traits>(
            max(args_offset + args_size, ret_offset + ret_size));

        auto const dest_address = address_from_uint256(address);

#if defined(MONAD_ZKVM_ZISK)
        auto const access_status =
            host_of(*ctx).access_account(host_shim::addr(&dest_address));
#else
        auto const access_status =
            ctx->host->access_account(ctx->context, &dest_address);
#endif
        if (access_status == EVMC_ACCESS_COLD) {
            ctx->deduct_gas(traits::cold_account_cost());
        }

#if defined(MONAD_ZKVM_ZISK)
        // The message's addresses bound where they lie, not copied into
        // locals of their own before being copied into the message: a
        // 20-byte copy each. EIP-7702: if the code address starts with
        // 0xEF0100, then treat it as a delegated call in the context of the
        // current authority; the delegate is initialised from the call's own
        // result, where an assignment is a 21-byte copy of the optional.
        std::optional<Address> const delegate_address =
            [&]() -> std::optional<Address> {
            if constexpr (traits::evm_rev() >= MONAD_ETH_PRAGUE) {
                return evm::resolve_delegation(
                    ctx->host, ctx->context, dest_address);
            }
            else {
                return std::nullopt;
            }
        }();
        Address const *code_address_p = &dest_address;
        if constexpr (traits::evm_rev() >= MONAD_ETH_PRAGUE) {
            if (delegate_address) {
                auto const access_status = host_of(*ctx).access_account(
                    host_shim::addr(&*delegate_address));
                ctx->gas_remaining -= (access_status == EVMC_ACCESS_COLD
                                           ? traits::cold_account_cost()
                                           : 0) +
                                      100;
                code_address_p = &*delegate_address;
            }
        }
        Address const &code_address = *code_address_p;

        Address const &recipient = (call_kind == EVMC_CALL || static_call)
                                       ? dest_address
                                       : ctx->env.recipient;

        Address const &sender = (call_kind == EVMC_DELEGATECALL)
                                    ? ctx->env.sender
                                    : ctx->env.recipient;
#else
        auto const code_address = [&]() -> Address {
            if constexpr (traits::evm_rev() >= MONAD_ETH_PRAGUE) {
                // EIP-7702: if the code address starts with 0xEF0100, then
                // treat it as a delegated call in the context of the
                // current authority.
                if (auto delegate_address = evm::resolve_delegation(
                        ctx->host, ctx->context, dest_address)) {
                    auto const access_status = ctx->host->access_account(
                        ctx->context, &*delegate_address);
                    ctx->gas_remaining -= (access_status == EVMC_ACCESS_COLD
                                               ? traits::cold_account_cost()
                                               : 0) +
                                          100;
                    return *delegate_address;
                }
            }
            return dest_address;
        }();

        auto const recipient = (call_kind == EVMC_CALL || static_call)
                                   ? dest_address
                                   : ctx->env.recipient;

        auto const sender = (call_kind == EVMC_DELEGATECALL)
                                ? ctx->env.sender
                                : ctx->env.recipient;
#endif

        if (has_value) {
            ctx->gas_remaining -= 9000;
        }

        if (call_kind == EVMC_CALL) {
            if (MONAD_UNLIKELY(
                    has_value && (ctx->env.evmc_flags & EVMC_STATIC))) {
                auto const error_code =
                    ctx->gas_remaining + remaining_block_base_gas < 0
                        ? StatusCode::OutOfGas
                        : StatusCode::Error;
                ctx->exit(error_code);
            }

            if (has_value &&
                !ctx->host->account_exists(ctx->context, &dest_address)) {
                ctx->gas_remaining -= 25000;
            }
        }

        auto const gas_left_here =
            ctx->gas_remaining + remaining_block_base_gas;

        if (MONAD_UNLIKELY(gas_left_here < 0)) {
            ctx->exit(StatusCode::OutOfGas);
        }

        auto gas = clamp_cast<int64_t>(gas_word);

        gas = std::min(gas, gas_left_here - (gas_left_here / 64));

        if (has_value) {
            gas += 2300;
            ctx->gas_remaining += 2300;
        }

        if (MONAD_UNLIKELY(ctx->env.depth >= 1024)) {
            return 0;
        }

        auto const message = evmc_message{
            .kind = call_kind,
            .flags = message_flags(
                static_cast<uint32_t>(ctx->env.evmc_flags),
                static_call,
                dest_address != code_address),
            .depth = static_cast<int32_t>(ctx->env.depth + 1),
            .gas = gas,
            .recipient = recipient,
            .sender = sender,
            .input_data =
                (*args_size > 0) ? ctx->memory.data + *args_offset : nullptr,
            .input_size = *args_size,
            .value = static_cast<evmc::bytes32>(value),
            .create2_salt = static_cast<evmc::bytes32>(ctx->env.create2_salt),
            .code_address = code_address,
            .memory_handle = ctx->memory.data_handle,
            .memory = ctx->memory.data + ctx->memory.size,
            .memory_capacity = ctx->memory.capacity - ctx->memory.size,
        };

#if defined(MONAD_ZKVM_ZISK)
        // What the C adapter does, without its frame.
        auto const result = host_of(*ctx).call(message).release_raw();
#else
        auto const result = ctx->host->call(ctx->context, &message);
#endif

        ctx->env.set_return_data(result.output_data, result.output_size);

        // Unwind the stack after setting return data, so that return data
        // is deallocated by the `Environment` destructor.
        ctx->propagate_stack_unwind();

        ctx->deduct_gas(gas - result.gas_left);
        ctx->gas_refund += result.gas_refund;

        auto const copy_size =
            std::min(static_cast<size_t>(*ret_size), result.output_size);
        std::copy_n(
            result.output_data, copy_size, ctx->memory.data + *ret_offset);

        return (result.status_code == EVMC_SUCCESS) ? 1 : 0;
    }

    EXPLICIT_TRAITS(call_impl);

    template <Traits traits>
    void call(
        Context *ctx, uint256_t *result_ptr, uint256_t const *gas_ptr,
        uint256_t const *address_ptr, uint256_t const *value_ptr,
        uint256_t const *args_offset_ptr, uint256_t const *args_size_ptr,
        uint256_t const *ret_offset_ptr, uint256_t const *ret_size_ptr,
        int64_t const remaining_block_base_gas)
    {
        *result_ptr = call_impl<traits>(
            ctx,
            *gas_ptr,
            *address_ptr,
            *value_ptr != 0,
            store_be_as<bytes32_t>(*value_ptr),
            *args_offset_ptr,
            *args_size_ptr,
            *ret_offset_ptr,
            *ret_size_ptr,
            EVMC_CALL,
            false,
            remaining_block_base_gas);
    }

    EXPLICIT_TRAITS(call);

    template <Traits traits>
    void callcode(
        Context *ctx, uint256_t *result_ptr, uint256_t const *gas_ptr,
        uint256_t const *address_ptr, uint256_t const *value_ptr,
        uint256_t const *args_offset_ptr, uint256_t const *args_size_ptr,
        uint256_t const *ret_offset_ptr, uint256_t const *ret_size_ptr,
        int64_t const remaining_block_base_gas)
    {
        *result_ptr = call_impl<traits>(
            ctx,
            *gas_ptr,
            *address_ptr,
            *value_ptr != 0,
            store_be_as<bytes32_t>(*value_ptr),
            *args_offset_ptr,
            *args_size_ptr,
            *ret_offset_ptr,
            *ret_size_ptr,
            EVMC_CALLCODE,
            false,
            remaining_block_base_gas);
    }

    EXPLICIT_TRAITS(callcode);

    template <Traits traits>
    void delegatecall(
        Context *ctx, uint256_t *result_ptr, uint256_t const *gas_ptr,
        uint256_t const *address_ptr, uint256_t const *args_offset_ptr,
        uint256_t const *args_size_ptr, uint256_t const *ret_offset_ptr,
        uint256_t const *ret_size_ptr, int64_t const remaining_block_base_gas)
    {
        *result_ptr = call_impl<traits>(
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

    EXPLICIT_TRAITS(delegatecall);

    template <Traits traits>
    void staticcall(
        Context *ctx, uint256_t *result_ptr, uint256_t const *gas_ptr,
        uint256_t const *address_ptr, uint256_t const *args_offset_ptr,
        uint256_t const *args_size_ptr, uint256_t const *ret_offset_ptr,
        uint256_t const *ret_size_ptr, int64_t const remaining_block_base_gas)
    {
        static_assert(traits::evm_rev() >= MONAD_ETH_CONSTANTINOPLE);

        *result_ptr = call_impl<traits>(
            ctx,
            *gas_ptr,
            *address_ptr,
            false,
            bytes32_t{},
            *args_offset_ptr,
            *args_size_ptr,
            *ret_offset_ptr,
            *ret_size_ptr,
            EVMC_CALL,
            true,
            remaining_block_base_gas);
    }

    EXPLICIT_TRAITS(staticcall);
}
