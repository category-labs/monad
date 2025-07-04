#pragma once

#include <monad/vm/core/assert.h>
#include <monad/vm/runtime/transmute.hpp>
#include <monad/vm/runtime/types.hpp>
#include <monad/vm/runtime/uint256.hpp>

#include <evmc/evmc.hpp>

namespace monad::vm::runtime
{
    template <evmc_revision Rev>
    void selfdestruct [[noreturn]] (Context *ctx, uint256_t const *address_ptr)
    {
        if (ctx->env.evmc_flags == EVMC_STATIC) {
            ctx->exit(StatusCode::Error);
        }

        auto address = address_from_uint256(*address_ptr);

        if constexpr (Rev >= EVMC_BERLIN) {
            auto access_status =
                ctx->host->access_account(ctx->context, &address);
            if (access_status == EVMC_ACCESS_COLD) {
                ctx->deduct_gas(2600);
            }
        }

        if constexpr (Rev >= EVMC_TANGERINE_WHISTLE) {
            auto non_zero_transfer = [ctx] {
                if constexpr (Rev == EVMC_TANGERINE_WHISTLE) {
                    return true;
                }
                auto balance =
                    ctx->host->get_balance(ctx->context, &ctx->env.recipient);
                return balance != evmc::bytes32{};
            }();

            if (non_zero_transfer) {
                auto exists = ctx->host->account_exists(ctx->context, &address);

                if (!exists) {
                    ctx->deduct_gas(25000);
                }
            }
        }

        auto result = ctx->host->selfdestruct(
            ctx->context, &ctx->env.recipient, &address);

        if constexpr (Rev < EVMC_LONDON) {
            if (result) {
                ctx->gas_refund += 24000;
            }
        }

        ctx->exit(StatusCode::Success);
    }
}
