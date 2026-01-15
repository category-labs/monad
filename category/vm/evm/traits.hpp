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

#include <category/core/is_specialization_of.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/evm/monad/revision.h>

#include <evmc/evmc.h>

#include <concepts>
#include <limits>
#include <utility>

namespace monad
{
    namespace constants
    {
        inline constexpr size_t MAX_CODE_SIZE_EIP170 = 24 * 1024; // 0x6000
        inline constexpr size_t MAX_INITCODE_SIZE_EIP3860 =
            2 * MAX_CODE_SIZE_EIP170; // 0xC000

        inline constexpr size_t MAX_CODE_SIZE_MONAD_TWO = 128 * 1024;
        inline constexpr size_t MAX_INITCODE_SIZE_MONAD_FOUR =
            2 * MAX_CODE_SIZE_MONAD_TWO;
    }

    template <typename T>
    concept Traits = requires() {
        requires sizeof(T) == 1;
        { T::evm_rev() } -> std::same_as<evmc_revision>;

        // Feature flags
        { T::eip_2565_active() } -> std::same_as<bool>;
        { T::eip_2929_active() } -> std::same_as<bool>;
        { T::eip_4844_active() } -> std::same_as<bool>;
        { T::eip_7823_active() } -> std::same_as<bool>;
        { T::eip_7883_active() } -> std::same_as<bool>;
        { T::eip_7951_active() } -> std::same_as<bool>;
        { T::can_create_inside_delegated() } -> std::same_as<bool>;

        // Constants
        { T::max_code_size() } -> std::same_as<size_t>;
        { T::max_initcode_size() } -> std::same_as<size_t>;
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
        static consteval evmc_revision evm_rev() noexcept
        {
            return Rev;
        }

        static consteval bool eip_2565_active() noexcept
        {
            return Rev >= EVMC_BERLIN;
        }

        static consteval bool eip_2929_active() noexcept
        {
            return Rev >= EVMC_BERLIN;
        }

        static consteval bool eip_4844_active() noexcept
        {
            return Rev >= EVMC_CANCUN;
        }

        static consteval bool eip_7823_active() noexcept
        {
            return Rev >= EVMC_OSAKA;
        }

        static consteval bool eip_7883_active() noexcept
        {
            return Rev >= EVMC_OSAKA;
        }

        static consteval bool eip_7951_active() noexcept
        {
            return Rev >= EVMC_OSAKA;
        }

        static consteval bool can_create_inside_delegated() noexcept
        {
            return true;
        }

        static consteval size_t max_code_size() noexcept
        {
            if constexpr (Rev >= EVMC_SPURIOUS_DRAGON) {
                return constants::MAX_CODE_SIZE_EIP170;
            }

            return std::numeric_limits<size_t>::max();
        }

        static consteval size_t max_initcode_size() noexcept
        {
            if constexpr (Rev >= EVMC_SHANGHAI) {
                return constants::MAX_INITCODE_SIZE_EIP3860;
            }

            return std::numeric_limits<size_t>::max();
        }

        static consteval int64_t cold_account_cost() noexcept
        {
            if constexpr (eip_2929_active()) {
                return 2500;
            }

            std::unreachable();
        }

        static consteval int64_t cold_storage_cost() noexcept
        {
            if constexpr (eip_2929_active()) {
                return 2000;
            }

            std::unreachable();
        }

        static consteval uint64_t id() noexcept
        {
            return static_cast<uint64_t>(Rev);
        }
    };

    template <monad_revision Rev>
    struct MonadTraits
    {
        static consteval evmc_revision evm_rev() noexcept
        {
            if constexpr (Rev >= MONAD_NEXT) {
                return EVMC_OSAKA;
            }
            if constexpr (Rev >= MONAD_FOUR) {
                return EVMC_PRAGUE;
            }

            return EVMC_CANCUN;
        }

        static consteval monad_revision monad_rev() noexcept
        {
            return Rev;
        }

        static consteval bool eip_2565_active() noexcept
        {
            return evm_rev() >= EVMC_BERLIN;
        }

        static consteval bool eip_2929_active() noexcept
        {
            return evm_rev() >= EVMC_BERLIN;
        }

        static consteval bool eip_4844_active() noexcept
        {
            // if this EIP is ever enabled, reserve balance must be modified
            // such that execution (and consensus) is accounting for the blob
            // gas used (irrevocable) in the reserve balance calculation
            return false;
        }

        static consteval bool eip_7823_active() noexcept
        {
            return evm_rev() >= EVMC_OSAKA;
        }

        static consteval bool eip_7883_active() noexcept
        {
            return evm_rev() >= EVMC_OSAKA;
        }

        static consteval bool eip_7951_active() noexcept
        {
            return Rev >= MONAD_FOUR;
        }

        static consteval bool can_create_inside_delegated() noexcept
        {
            return false;
        }

        // Pricing version 1 activates the changes in:
        // Monad specification §4: Opcode Gas Costs and Gas Refunds
        static consteval uint8_t monad_pricing_version() noexcept
        {
            if constexpr (Rev >= MONAD_SEVEN) {
                return 1;
            }

            return 0;
        }

        static consteval size_t max_code_size() noexcept
        {
            if constexpr (Rev >= MONAD_TWO) {
                return constants::MAX_CODE_SIZE_MONAD_TWO;
            }

            return constants::MAX_CODE_SIZE_EIP170;
        }

        static consteval size_t max_initcode_size() noexcept
        {
            if constexpr (Rev >= MONAD_FOUR) {
                return constants::MAX_INITCODE_SIZE_MONAD_FOUR;
            }

            return constants::MAX_INITCODE_SIZE_EIP3860;
        }

        static consteval int64_t cold_account_cost() noexcept
        {
            if constexpr (monad_pricing_version() >= 1) {
                return 10000;
            }
            else if constexpr (eip_2929_active()) {
                return 2500;
            }

            std::unreachable();
        }

        static consteval int64_t cold_storage_cost() noexcept
        {
            if constexpr (monad_pricing_version() >= 1) {
                return 8000;
            }
            else if constexpr (eip_2929_active()) {
                return 2000;
            }

            std::unreachable();
        }

        static consteval uint64_t id() noexcept
        {
            return static_cast<uint64_t>(Rev);
        }

        // Temporary workaround that should be considered equivalent to calling
        // evm_rev(); remove when the refactoring to use feature flags is
        // complete.
        using evm_base = EvmTraits<MonadTraits::evm_rev()>;
    };

    template <typename T>
    inline constexpr bool is_evm_trait_v = is_specialization_of_v<EvmTraits, T>;

    template <typename T>
    inline constexpr bool is_monad_trait_v =
        is_specialization_of_v<MonadTraits, T>;

    static_assert(is_monad_trait_v<MonadTraits<MONAD_ZERO>> == true);
    static_assert(is_monad_trait_v<EvmTraits<EVMC_FRONTIER>> == false);
    static_assert(is_evm_trait_v<MonadTraits<MONAD_ZERO>> == false);
    static_assert(is_evm_trait_v<EvmTraits<EVMC_FRONTIER>> == true);
}
