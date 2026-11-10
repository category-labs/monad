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

#include <category/core/likely.h>
#include <category/core/runtime/uint256.hpp>
#include <category/vm/evm/access_status.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/message.hpp>
#include <category/vm/evm/revision.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/host.hpp>
#include <category/vm/runtime/call_host.hpp>
#include <category/vm/runtime/selfdestruct.hpp>
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/types.hpp>

#include <utility>

namespace monad::vm::runtime
{
    template <Traits traits>
    void selfdestruct [[noreturn]] (Context *ctx, uint256_t const *address_ptr)
    {
        static_assert(traits::evm_rev() >= EvmRevision::Berlin);

        if (MONAD_UNLIKELY(
                ctx->env.flags & std::to_underlying(CallFlags::Static))) {
            ctx->exit(StatusCode::Error);
        }

        auto const address = address_from_uint256(*address_ptr);

        auto const access_status =
            call_host<&Host::access_account>(ctx, address);
        if (access_status == AccessStatus::Cold) {
            // +100 for the warm account access cost.
            ctx->deduct_gas(traits::cold_account_cost() + 100);
        }

        auto const non_zero_transfer =
            call_host<&Host::get_balance>(ctx, ctx->env.recipient) != 0;

        if (non_zero_transfer) {
            auto const exists = call_host<&Host::account_exists>(ctx, address);

            if (!exists) {
                ctx->deduct_gas(25000);
            }
        }

        auto const result =
            call_host<&Host::selfdestruct>(ctx, ctx->env.recipient, address);

        if constexpr (!traits::eip_3529_active()) {
            if (result) {
                ctx->gas_refund += 24000;
            }
        }

        ctx->exit(StatusCode::Success);
    }

    EXPLICIT_TRAITS(selfdestruct);
}
