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
#include <category/vm/evm/chain.hpp>
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/runtime/uint256.hpp>

#include <evmc/evmc.hpp>

namespace monad::vm::runtime
{
    template <Traits traits>
    void selfdestruct [[noreturn]] (Context *ctx, uint256_t const *address_ptr)
    {
        if (MONAD_VM_UNLIKELY(ctx->env.evmc_flags & EVMC_STATIC)) {
            ctx->exit(StatusCode::Error);
        }

        auto address = address_from_uint256(*address_ptr);

        if constexpr (traits::evm_rev() >= EVMC_BERLIN) {
            auto access_status =
                ctx->host->access_account(ctx->context, &address);
            if (access_status == EVMC_ACCESS_COLD) {
                ctx->deduct_gas(2600);
            }
        }

        if constexpr (traits::evm_rev() >= EVMC_TANGERINE_WHISTLE) {
            auto non_zero_transfer = [ctx] {
                if constexpr (traits::evm_rev() == EVMC_TANGERINE_WHISTLE) {
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

        if constexpr (traits::evm_rev() < EVMC_LONDON) {
            if (result) {
                ctx->gas_refund += 24000;
            }
        }

        ctx->exit(StatusCode::Success);
    }
}
