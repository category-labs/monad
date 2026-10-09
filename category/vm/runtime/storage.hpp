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
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#if defined(MONAD_ZKVM_ZISK)
    #include <category/vm/host.hpp>
    #include <category/vm/runtime/storage_costs.hpp>
#endif
#include <category/vm/runtime/types.hpp>

#include <cstdint>

namespace monad::vm::runtime
{
#if defined(MONAD_ZKVM_ZISK)
    // Inline on ZisK, as tload is: called from SLOAD's handler, it was a
    // call and a frame of its own on every SLOAD, inside the handler's.
    // Both host calls in one. A cold access that the gas left cannot pay
    // for exits below, before the value is read, as it did between them.
    template <Traits traits>
    [[gnu::always_inline]] inline void
    sload(Context *ctx, uint256_t *result_ptr, uint256_t const *key_ptr)
    {
        static_assert(traits::evm_rev() >= MONAD_ETH_BERLIN);

        // The key is copied out first: the value is written over it, in the
        // stack's word order.
        auto key = store_be_as<bytes32_t>(*key_ptr);
        if (guest_sload_into<traits>(
                host_of(*ctx),
                host_shim::addr(&ctx->env.recipient),
                host_shim::word(&key),
                ctx->gas_remaining >= traits::cold_storage_cost(),
                *result_ptr) == EVMC_ACCESS_COLD) {
            ctx->deduct_gas(traits::cold_storage_cost());
        }
    }

    // SSTORE's, inline on ZisK for the same reason.
    template <Traits traits>
    [[gnu::always_inline]] inline void sstore(
        Context *ctx, uint256_t const *key_ptr, uint256_t const *value_ptr,
        int64_t const remaining_block_base_gas)
    {
        static_assert(traits::evm_rev() >= MONAD_ETH_BERLIN);

        if (MONAD_UNLIKELY(ctx->env.evmc_flags & evmc_flags::EVMC_STATIC)) {
            ctx->exit(StatusCode::Error);
        }

        constexpr auto min_gas = minimum_store_gas<traits>();

        // EIP-2200
        if (ctx->gas_remaining + remaining_block_base_gas + min_gas <= 2300) {
            ctx->exit(StatusCode::OutOfGas);
        }

        auto key = store_be_as<bytes32_t>(*key_ptr);
        auto value = store_be_as<bytes32_t>(*value_ptr);

        if constexpr (traits::mip_8_active()) {
            auto const access_status = ctx->host->access_storage(
                ctx->context, &ctx->env.recipient, &key);
            if (access_status == EVMC_ACCESS_COLD) {
                ctx->deduct_gas(traits::cold_storage_cost());
            }

            auto const storage_status = ctx->host->set_storage(
                ctx->context, &ctx->env.recipient, &key, &value);

            auto const [first_page_write, grew_state] = ctx->host->update_page(
                ctx->context, &ctx->env.recipient, &key, storage_status);

            int64_t gas_used = traits::base_sstore_cost();
            if (first_page_write) {
                gas_used += traits::page_write_cost();
            }
            if (grew_state) {
                gas_used += traits::page_growth_cost();
            }

            gas_used -= min_gas;
            ctx->deduct_gas(gas_used);
        }
        else {
            // Both host calls in one. A cold access that the gas left cannot
            // pay for exits below, before the write, as it did between them.
            auto const [access_status, storage_status] =
                guest_sstore_into<traits>(
                    host_of(*ctx),
                    host_shim::addr(&ctx->env.recipient),
                    host_shim::word(&key),
                    host_shim::word(&value),
                    ctx->gas_remaining >=
                        traits::cold_storage_cost() + min_gas);
            if (access_status == MONAD_ACCESS_COLD) {
                ctx->deduct_gas(traits::cold_storage_cost() + min_gas);
            }

            auto [gas_used, gas_refund] =
                store_cost<traits>(to_evmc_storage_status(storage_status));

            gas_used -= min_gas;

            ctx->gas_refund += gas_refund;
            ctx->deduct_gas(gas_used);
        }
    }
#else
    template <Traits traits>
    void sload(Context *ctx, uint256_t *result_ptr, uint256_t const *key_ptr);

    template <Traits traits>
    void sstore(
        Context *ctx, uint256_t const *key_ptr, uint256_t const *value_ptr,
        int64_t remaining_block_base_gas);
#endif

    inline void tload(
        Context *const ctx, uint256_t *const result_ptr,
        uint256_t const *const key_ptr)
    {
        auto key = store_be_as<bytes32_t>(*key_ptr);

#if defined(MONAD_ZKVM_ZISK)
        // As SLOAD: the host's method, not its C adapter.
        auto const value = guest_get_transient_storage(
            host_of(*ctx),
            host_shim::addr(&ctx->env.recipient),
            host_shim::word(&key));
#else
        auto const value = ctx->host->get_transient_storage(
            ctx->context, &ctx->env.recipient, &key);
#endif

        *result_ptr = load_be<uint256_t>(value);
    }

    inline void tstore(
        Context *const ctx, uint256_t const *const key_ptr,
        uint256_t const *const val_ptr)
    {
        if (MONAD_UNLIKELY(ctx->env.evmc_flags & evmc_flags::EVMC_STATIC)) {
            ctx->exit(StatusCode::Error);
        }

        auto key = store_be_as<bytes32_t>(*key_ptr);
        auto val = store_be_as<bytes32_t>(*val_ptr);

#if defined(MONAD_ZKVM_ZISK)
        guest_set_transient_storage(
            host_of(*ctx),
            host_shim::addr(&ctx->env.recipient),
            host_shim::word(&key),
            host_shim::word(&val));
#else
        ctx->host->set_transient_storage(
            ctx->context, &ctx->env.recipient, &key, &val);
#endif
    }

    bool debug_tstore_stack(
        Context const *ctx, uint256_t const *stack, uint64_t stack_size,
        uint64_t offset, uint64_t base_offset);
}
