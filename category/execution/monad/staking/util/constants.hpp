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

#include <cstdint>
#include <memory>
#include <optional>
#include <span>

#include <intx/intx.hpp>

MONAD_STAKING_NAMESPACE_BEGIN

using namespace intx::literals;

inline constexpr uint256_t MON{1000000000000000000_u256};

inline constexpr uint256_t MIN_VALIDATE_STAKE{1'000'000 * MON};
inline constexpr uint256_t ACTIVE_VALIDATOR_STAKE{50'000'000 * MON};
inline constexpr uint256_t UNIT_BIAS{100000000000000000000000000000_u256};

inline constexpr Address STAKING_CA{0x1000};
inline constexpr uint64_t ACTIVE_VALSET_SIZE{200};
inline constexpr uint64_t WITHDRAWAL_DELAY = 1;

enum
{
    ValidatorFlagsOk = 0,
    ValidatorFlagsStakeTooLow = (1 << 0),
    ValidatorFlagWithdrawn = (1 << 1),
    ValidatorFlagsDoubleSign = (1 << 2),
};

MONAD_STAKING_NAMESPACE_END
