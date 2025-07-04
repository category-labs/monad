#pragma once

#include <monad/vm/core/assert.h>
#include <monad/vm/runtime/storage_costs.hpp>
#include <monad/vm/runtime/transmute.hpp>
#include <monad/vm/runtime/types.hpp>
#include <monad/vm/runtime/uint256.hpp>

#include <evmc/evmc.hpp>

#include <array>

namespace monad::vm::runtime
{
    template <evmc_revision Rev>
    void sload(Context *ctx, uint256_t *result_ptr, uint256_t const *key_ptr)
    {
        auto key = bytes32_from_uint256(*key_ptr);

        if constexpr (Rev >= EVMC_BERLIN) {
            auto access_status = ctx->host->access_storage(
                ctx->context, &ctx->env.recipient, &key);
            if (access_status == EVMC_ACCESS_COLD) {
                ctx->deduct_gas(2000);
            }
        }

        auto value =
            ctx->host->get_storage(ctx->context, &ctx->env.recipient, &key);

        *result_ptr = uint256_from_bytes32(value);
    }

    template <evmc_revision Rev>
    void sstore(
        Context *ctx, uint256_t const *key_ptr, uint256_t const *value_ptr,
        std::int64_t remaining_block_base_gas)
    {
        if (ctx->env.evmc_flags == evmc_flags::EVMC_STATIC) {
            ctx->exit(StatusCode::Error);
        }

        constexpr auto min_gas = minimum_store_gas<Rev>();

        // EIP-2200
        if constexpr (Rev >= EVMC_ISTANBUL) {
            if (ctx->gas_remaining + remaining_block_base_gas + min_gas <=
                2300) {
                ctx->exit(StatusCode::OutOfGas);
            }
        }

        auto key = bytes32_from_uint256(*key_ptr);
        auto value = bytes32_from_uint256(*value_ptr);

        auto access_status = EVMC_ACCESS_COLD;
        if constexpr (Rev >= EVMC_BERLIN) {
            access_status = ctx->host->access_storage(
                ctx->context, &ctx->env.recipient, &key);
        }

        auto storage_status = ctx->host->set_storage(
            ctx->context, &ctx->env.recipient, &key, &value);

        auto [gas_used, gas_refund] = store_cost<Rev>(storage_status);

        // The code generator has taken care of accounting for the minimum base
        // gas cost of this SSTORE already, but to keep the table of costs
        // readable it encodes the total gas usage of each combination, rather
        // than the amount relative to the minimum gas.
        gas_used -= min_gas;

        if constexpr (Rev >= EVMC_BERLIN) {
            if (access_status == EVMC_ACCESS_COLD) {
                gas_used += 2100;
            }
        }

        ctx->gas_refund += gas_refund;
        ctx->deduct_gas(gas_used);
    }

    inline void
    tload(Context *ctx, uint256_t *result_ptr, uint256_t const *key_ptr)
    {
        auto key = bytes32_from_uint256(*key_ptr);

        auto value = ctx->host->get_transient_storage(
            ctx->context, &ctx->env.recipient, &key);

        *result_ptr = uint256_from_bytes32(value);
    }

    inline void
    tstore(Context *ctx, uint256_t const *key_ptr, uint256_t const *val_ptr)
    {
        if (ctx->env.evmc_flags == evmc_flags::EVMC_STATIC) {
            ctx->exit(StatusCode::Error);
        }

        auto key = bytes32_from_uint256(*key_ptr);
        auto val = bytes32_from_uint256(*val_ptr);

        ctx->host->set_transient_storage(
            ctx->context, &ctx->env.recipient, &key, &val);
    }

    bool debug_tstore_stack(
        Context const *ctx, uint256_t const *stack, uint64_t stack_size,
        uint64_t offset, uint64_t base_offset);
}
