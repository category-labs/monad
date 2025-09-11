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
#include <category/vm/evm/monad/revision.h>

#include <evmc/evmc.h>

#include <concepts>
#include <utility>

namespace monad
{
    template <typename T>
    concept Traits = requires() {
        requires sizeof(T) == 1;
        { T::evm_rev() } -> std::same_as<evmc_revision>;
        { T::monad_rev() } -> std::same_as<monad_revision>;

        // Feature flags
        { T::eip_2929_active() } -> std::same_as<bool>;
        { T::eip_7951_active() } -> std::same_as<bool>;
        { T::can_create_inside_delegated() } -> std::same_as<bool>;

        // Monad specification §2.3: Payment Rule for User
        { T::should_refund_reduce_gas_used() } -> std::same_as<bool>;
        { T::eip_7702_refund_active() } -> std::same_as<bool>;

        // Pricing version 1 activates the changes in:
        // Monad specification §4: Opcode Gas Costs and Gas Refunds
        { T::monad_pricing_version() } -> std::same_as<uint8_t>;

        // Constants
        { T::cold_account_cost() } -> std::same_as<int64_t>;
        { T::cold_storage_cost() } -> std::same_as<int64_t>;

        // Instead of storing a revision, caches should identify revision
        // changes by storing the opaque value returned by this method. No
        // two chain specializations will return the same value, but no
        // further semantics should be associated with the return value.
        { T::id() } -> std::same_as<uint64_t>;
    };

    template <evmc_revision Rev>
    struct EvmTraits
    {
        static constexpr evmc_revision evm_rev() noexcept
        {
            return Rev;
        }

        static constexpr monad_revision monad_rev() noexcept
        {
            static_assert(false, "Calling monad_rev() on an EVM trait type");
            std::unreachable();
        }

        static constexpr bool eip_2929_active() noexcept
        {
            return Rev >= EVMC_BERLIN;
        }

        static constexpr bool eip_7951_active() noexcept
        {
            return Rev >= EVMC_OSAKA;
        }

        static constexpr bool can_create_inside_delegated() noexcept
        {
            return true;
        }

        static constexpr uint8_t monad_pricing_version() noexcept
        {
            static_assert(
                false, "Calling monad_pricing_version() on an EVM trait type");
            std::unreachable();
        }

        static constexpr bool should_refund_reduce_gas_used() noexcept
        {
            return true;
        }

        static constexpr bool eip_7702_refund_active() noexcept
        {
            return Rev >= EVMC_PRAGUE;
        }

        static constexpr int64_t cold_account_cost() noexcept
        {
            if constexpr (eip_2929_active()) {
                return 2500;
            }

            std::unreachable();
        }

        static constexpr int64_t cold_storage_cost() noexcept
        {
            if constexpr (eip_2929_active()) {
                return 2000;
            }

            std::unreachable();
        }

        static constexpr uint64_t id() noexcept
        {
            return static_cast<uint64_t>(Rev);
        }
    };

    template <monad_revision Rev>
    struct MonadTraits
    {
        static constexpr evmc_revision evm_rev() noexcept
        {
            if constexpr (Rev >= MONAD_FOUR) {
                return EVMC_PRAGUE;
            }

            return EVMC_CANCUN;
        }

        static constexpr monad_revision monad_rev() noexcept
        {
            return Rev;
        }

        static constexpr bool eip_2929_active() noexcept
        {
            return evm_rev() >= EVMC_BERLIN;
        }

        static constexpr bool eip_7951_active() noexcept
        {
            return Rev >= MONAD_FOUR;
        }

        static constexpr bool can_create_inside_delegated() noexcept
        {
            return false;
        }

        static constexpr uint8_t monad_pricing_version() noexcept
        {
            if constexpr (Rev >= MONAD_FOUR) {
                return 1;
            }

            return 0;
        }

        static constexpr bool should_refund_reduce_gas_used() noexcept
        {
            return Rev < MONAD_FOUR;
        }

        static constexpr bool eip_7702_refund_active() noexcept
        {
            return false;
        }

        static constexpr int64_t cold_account_cost() noexcept
        {
            if constexpr (monad_pricing_version() >= 1) {
                return 10000;
            }
            else if constexpr (eip_2929_active()) {
                return 2500;
            }

            std::unreachable();
        }

        static constexpr int64_t cold_storage_cost() noexcept
        {
            if constexpr (monad_pricing_version() >= 1) {
                return 8000;
            }
            else if constexpr (eip_2929_active()) {
                return 2000;
            }

            std::unreachable();
        }

        static constexpr uint64_t id() noexcept
        {
            return static_cast<uint64_t>(Rev);
        }

        // Temporary workaround that should be considered equivalent to calling
        // evm_rev(); remove when the refactoring to use feature flags is
        // complete.
        using evm_base = EvmTraits<MonadTraits::evm_rev()>;
    };
}
