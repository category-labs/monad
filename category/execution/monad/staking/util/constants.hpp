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

#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/core/contract/storage_variable.hpp>
#include <category/execution/monad/staking/config.hpp>
#include <category/vm/evm/traits.hpp>

#include <cstdint>
#include <limits>
#include <memory>
#include <optional>
#include <span>

#include <intx/intx.hpp>

MONAD_STAKING_NAMESPACE_BEGIN

using namespace intx::literals;

// staking contract address
inline constexpr Address STAKING_CA{0x1000};

// 1e18 constant
inline constexpr uint256_t MON{1000000000000000000_u256};

// accumulator precision
inline constexpr uint256_t UNIT_BIAS{
    1000000000000000000000000000000000000_u256}; // 1e36

// Results for get_valset, get_delegators_for_validator, and
// get_validators_for_delegator are paginated
inline constexpr uint64_t PAGINATED_RESULTS_SIZE{100};

struct Limits
{
    static constexpr uint256_t dust_threshold()
    {
        return 1000000000; // 1e9
    }

    static constexpr uint256_t max_commission()
    {
        return MON; // 1e18
    }

    template <Traits traits>
    static constexpr uint256_t active_validator_stake()
    {
        return 25'000'000 * MON;
    }

    static constexpr uint256_t min_auth_address_stake()
    {
        return 100'000 * MON;
    }

    static constexpr uint256_t min_external_reward()
    {
        return dust_threshold();
    }

    static constexpr uint256_t max_external_reward()
    {
        return 10000000000000000000000000_u256; // 1e25
    };

    static constexpr uint64_t active_valset_size()
    {
        return 200;
    }

    static constexpr uint64_t withdrawal_delay()
    {
        return 1;
    }
};

// sanity check: commission rate doesn't exceed 100% (1e18)
// note that: delegator_reward = (raw_reward * COMMISSION) / 1e18
static_assert(Limits::max_commission() <= MON);

enum
{
    ValidatorFlagsOk = 0,
    ValidatorFlagsStakeTooLow = (1 << 0),
    ValidatorFlagWithdrawn = (1 << 1),
    ValidatorFlagsDoubleSign = (1 << 2),
};

MONAD_STAKING_NAMESPACE_END
