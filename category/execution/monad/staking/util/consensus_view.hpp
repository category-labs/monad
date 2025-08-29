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

#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/core/contract/storage_variable.hpp>
#include <category/execution/monad/staking/config.hpp>

MONAD_NAMESPACE_BEGIN

class State;

MONAD_NAMESPACE_END

MONAD_STAKING_NAMESPACE_BEGIN

class ConsensusView
{
    State &state_;
    Address const &address_;
    uint256_t const key_;

    using Stake_t = u256_be;
    using Commission_t = u256_be;

    struct Offsets
    {
        static constexpr size_t stake = 0;
        static constexpr size_t commission =
            stake + StorageVariable<Stake_t>::N;
    };

public:
    ////////////
    // Layout //
    ////////////

    ConsensusView(State &state, Address const &address, bytes32_t const &key);

    StorageVariable<Stake_t> stake() noexcept
    {
        return {state_, address_, key_ + Offsets::stake};
    }

    StorageVariable<Stake_t> commission() noexcept
    {
        return {state_, address_, key_ + Offsets::commission};
    }
};

// SnapshotView is a copy of the consensus view
using SnapshotView = ConsensusView;

MONAD_STAKING_NAMESPACE_END
