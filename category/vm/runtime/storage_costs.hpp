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

#include <category/vm/evm/opcodes.hpp>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.hpp>

#include <array>
#include <cstdint>

namespace monad::vm::runtime
{
    struct StoreCost
    {
        std::int64_t gas_cost;
        std::int64_t gas_refund;
    };

    template <Traits traits>
    struct StorageCostTable
    {
        static constexpr std::array<StoreCost, 9> costs{};
    };

    template <Traits traits>
    static consteval std::int64_t minimum_store_gas()
    {
        constexpr auto costs = StorageCostTable<traits>::costs;
        constexpr auto min_gas =
            std::min_element(costs.begin(), costs.end(), [](auto ca, auto cb) {
                return ca.gas_cost < cb.gas_cost;
            })->gas_cost;
        static_assert(
            compiler::opcode_table<traits>[compiler::SSTORE].min_gas ==
            min_gas);
        return min_gas;
    }

    template <Traits traits>
    constexpr StoreCost store_cost(evmc_storage_status status)
    {
        return StorageCostTable<traits>::costs[status];
    }

    template <>
    struct StorageCostTable<EvmTraits<EVMC_FRONTIER>>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
        };
    };

    template <>
    struct StorageCostTable<EvmTraits<EVMC_HOMESTEAD>>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
        };
    };

    template <>
    struct StorageCostTable<EvmTraits<EVMC_TANGERINE_WHISTLE>>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
        };
    };

    template <>
    struct StorageCostTable<EvmTraits<EVMC_SPURIOUS_DRAGON>>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
        };
    };

    template <>
    struct StorageCostTable<EvmTraits<EVMC_BYZANTIUM>>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
        };
    };

    template <>
    struct StorageCostTable<EvmTraits<EVMC_CONSTANTINOPLE>>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 200, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 200, .gas_refund = -15000},
            StoreCost{.gas_cost = 200, .gas_refund = 15000},
            StoreCost{.gas_cost = 200, .gas_refund = -10200},
            StoreCost{.gas_cost = 200, .gas_refund = 19800},
            StoreCost{.gas_cost = 200, .gas_refund = 4800},
        };
    };

    template <>
    struct StorageCostTable<EvmTraits<EVMC_PETERSBURG>>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
        };
    };

    template <>
    struct StorageCostTable<EvmTraits<EVMC_ISTANBUL>>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 800, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 5000, .gas_refund = 15000},
            StoreCost{.gas_cost = 5000, .gas_refund = 0},
            StoreCost{.gas_cost = 800, .gas_refund = -15000},
            StoreCost{.gas_cost = 800, .gas_refund = 15000},
            StoreCost{.gas_cost = 800, .gas_refund = -10800},
            StoreCost{.gas_cost = 800, .gas_refund = 19200},
            StoreCost{.gas_cost = 800, .gas_refund = 4200},
        };
    };

    template <>
    struct StorageCostTable<EvmTraits<EVMC_BERLIN>>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 100, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 2900, .gas_refund = 15000},
            StoreCost{.gas_cost = 2900, .gas_refund = 0},
            StoreCost{.gas_cost = 100, .gas_refund = -15000},
            StoreCost{.gas_cost = 100, .gas_refund = 15000},
            StoreCost{.gas_cost = 100, .gas_refund = -12200},
            StoreCost{.gas_cost = 100, .gas_refund = 19900},
            StoreCost{.gas_cost = 100, .gas_refund = 2800},
        };
    };

    template <>
    struct StorageCostTable<EvmTraits<EVMC_LONDON>>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 100, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 2900, .gas_refund = 4800},
            StoreCost{.gas_cost = 2900, .gas_refund = 0},
            StoreCost{.gas_cost = 100, .gas_refund = -4800},
            StoreCost{.gas_cost = 100, .gas_refund = 4800},
            StoreCost{.gas_cost = 100, .gas_refund = -2000},
            StoreCost{.gas_cost = 100, .gas_refund = 19900},
            StoreCost{.gas_cost = 100, .gas_refund = 2800},
        };
    };

    template <>
    struct StorageCostTable<EvmTraits<EVMC_PARIS>>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 100, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 2900, .gas_refund = 4800},
            StoreCost{.gas_cost = 2900, .gas_refund = 0},
            StoreCost{.gas_cost = 100, .gas_refund = -4800},
            StoreCost{.gas_cost = 100, .gas_refund = 4800},
            StoreCost{.gas_cost = 100, .gas_refund = -2000},
            StoreCost{.gas_cost = 100, .gas_refund = 19900},
            StoreCost{.gas_cost = 100, .gas_refund = 2800},
        };
    };

    template <>
    struct StorageCostTable<EvmTraits<EVMC_SHANGHAI>>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 100, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 2900, .gas_refund = 4800},
            StoreCost{.gas_cost = 2900, .gas_refund = 0},
            StoreCost{.gas_cost = 100, .gas_refund = -4800},
            StoreCost{.gas_cost = 100, .gas_refund = 4800},
            StoreCost{.gas_cost = 100, .gas_refund = -2000},
            StoreCost{.gas_cost = 100, .gas_refund = 19900},
            StoreCost{.gas_cost = 100, .gas_refund = 2800},
        };
    };

    template <>
    struct StorageCostTable<EvmTraits<EVMC_CANCUN>>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 100, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 2900, .gas_refund = 4800},
            StoreCost{.gas_cost = 2900, .gas_refund = 0},
            StoreCost{.gas_cost = 100, .gas_refund = -4800},
            StoreCost{.gas_cost = 100, .gas_refund = 4800},
            StoreCost{.gas_cost = 100, .gas_refund = -2000},
            StoreCost{.gas_cost = 100, .gas_refund = 19900},
            StoreCost{.gas_cost = 100, .gas_refund = 2800},
        };
    };

    template <>
    struct StorageCostTable<EvmTraits<EVMC_PRAGUE>>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 100, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 2900, .gas_refund = 4800},
            StoreCost{.gas_cost = 2900, .gas_refund = 0},
            StoreCost{.gas_cost = 100, .gas_refund = -4800},
            StoreCost{.gas_cost = 100, .gas_refund = 4800},
            StoreCost{.gas_cost = 100, .gas_refund = -2000},
            StoreCost{.gas_cost = 100, .gas_refund = 19900},
            StoreCost{.gas_cost = 100, .gas_refund = 2800},
        };
    };

    template <>
    struct StorageCostTable<EvmTraits<EVMC_OSAKA>>
    {
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 100, .gas_refund = 0},
            StoreCost{.gas_cost = 20000, .gas_refund = 0},
            StoreCost{.gas_cost = 2900, .gas_refund = 4800},
            StoreCost{.gas_cost = 2900, .gas_refund = 0},
            StoreCost{.gas_cost = 100, .gas_refund = -4800},
            StoreCost{.gas_cost = 100, .gas_refund = 4800},
            StoreCost{.gas_cost = 100, .gas_refund = -2000},
            StoreCost{.gas_cost = 100, .gas_refund = 19900},
            StoreCost{.gas_cost = 100, .gas_refund = 2800},
        };
    };

    template <>
    struct StorageCostTable<MonadTraits<MONAD_ZERO>>
        : StorageCostTable<MonadTraits<MONAD_ZERO>::evm_base>
    {
    };

    template <>
    struct StorageCostTable<MonadTraits<MONAD_ONE>>
        : StorageCostTable<MonadTraits<MONAD_ONE>::evm_base>
    {
    };

    template <>
    struct StorageCostTable<MonadTraits<MONAD_TWO>>
        : StorageCostTable<MonadTraits<MONAD_TWO>::evm_base>
    {
    };

    template <>
    struct StorageCostTable<MonadTraits<MONAD_THREE>>
        : StorageCostTable<MonadTraits<MONAD_THREE>::evm_base>
    {
    };

    template <>
    struct StorageCostTable<MonadTraits<MONAD_FOUR>>
        : StorageCostTable<MonadTraits<MONAD_FOUR>::evm_base>
    {
    };

    template <>
    struct StorageCostTable<MonadTraits<MONAD_FIVE>>
    {
        // Derived from the algorithm in:
        // Monad specification §4.2: Storage Gas Cost and Refunds
        static constexpr auto costs = std::array{
            StoreCost{.gas_cost = 100, .gas_refund = 0}, // catch all
            StoreCost{.gas_cost = 127900, .gas_refund = 0}, // 0 -> 0 -> Z
            StoreCost{.gas_cost = 2900, .gas_refund = 120000}, // X -> X -> 0
            StoreCost{.gas_cost = 2900, .gas_refund = 0}, // X -> X -> Z
            StoreCost{.gas_cost = 100, .gas_refund = -120000}, // X -> 0 -> Z
            StoreCost{.gas_cost = 100, .gas_refund = 120000}, // X -> Y -> 0
            StoreCost{.gas_cost = 100, .gas_refund = -117200}, // X -> 0 -> X
            StoreCost{.gas_cost = 100, .gas_refund = 127800}, // 0 -> Y -> 0
            StoreCost{.gas_cost = 100, .gas_refund = 2800}, // X -> Y -> X
        };
    };
}
