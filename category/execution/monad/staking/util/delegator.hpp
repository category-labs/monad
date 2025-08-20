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

#include <category/core/byte_string.hpp>
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

// A struct in state containing all a delegators metadata.
class Delegator
{
    State &state_;
    Address const &address_;
    uint256_t const key_;

public:
    ///////////////////
    // Compact slots //
    ///////////////////
    struct Epochs
    {
        // stake that will be active next epoch
        u64_be delta_epoch;

        // stake that will be active next next epoch (delegate during boundary)
        u64_be next_delta_epoch;
    };

    static_assert(StorageVariable<Epochs>::N == 1);

    struct ListNode
    {
        // next and prev pointers in validator list
        u64_be inext;
        u64_be iprev;

        // next and prev pointers in delegator list
        Address anext;
        Address aprev;
    };

    static_assert(StorageVariable<ListNode>::N == 2);

    ////////////
    // Layout //
    ////////////
    using Stake_t = u256_be;
    using RewardsPerToken_t = u256_be;
    using Rewards_t = u256_be;
    using DeltaStake_t = u256_be;
    using NextDeltaStake_t = u256_be;
    using Epochs_t = Epochs;
    using ListNode_t = ListNode;

    struct Offsets
    {
        static constexpr size_t stake = 0;
        static constexpr size_t rewards_per_token =
            stake + StorageVariable<Stake_t>::N;
        static constexpr size_t rewards =
            rewards_per_token + StorageVariable<RewardsPerToken_t>::N;
        static constexpr size_t delta_stake =
            rewards + StorageVariable<Rewards_t>::N;
        static constexpr size_t next_delta_stake =
            delta_stake + StorageVariable<DeltaStake_t>::N;
        static constexpr size_t epochs =
            next_delta_stake + StorageVariable<NextDeltaStake_t>::N;
        static constexpr size_t list_node =
            epochs + StorageVariable<Epochs_t>::N;
    };

    Delegator(State &state, Address const &address, bytes32_t const key);

    /////////////
    // Getters //
    /////////////

    // currently active stake in the consensus
    StorageVariable<Stake_t> stake() noexcept
    {
        return {state_, address_, key_ + Offsets::stake};
    }

    // Last read reward per token accumulator. This is updated lazily whenever a
    // delegator action is performed.
    StorageVariable<RewardsPerToken_t> accumulated_reward_per_token() noexcept
    {
        return {state_, address_, key_ + Offsets::rewards_per_token};
    }

    // unclaimed rewards
    StorageVariable<Rewards_t> rewards() noexcept
    {
        return {state_, address_, key_ + Offsets::rewards};
    }

    // stake that will be active next epoch
    StorageVariable<DeltaStake_t> delta_stake() noexcept
    {
        return {state_, address_, key_ + Offsets::delta_stake};
    }

    // stake that will be active next next epoch (delegate during boundary)
    StorageVariable<NextDeltaStake_t> next_delta_stake() noexcept
    {
        return {state_, address_, key_ + Offsets::next_delta_stake};
    }

    // low level getter returning packed epochs for delta epoch and next delta
    // epoch. prefer the helpers for getting those values individually.
    StorageVariable<Epochs_t> epochs() noexcept
    {
        return {state_, address_, key_ + Offsets::epochs};
    }

    // list nodes that point to two things:
    //  1. next validator ID
    //  2. next delegator address
    StorageVariable<ListNode> list_node() noexcept
    {
        return {state_, address_, key_ + Offsets::list_node};
    }

    /////////////
    // Helpers //
    /////////////

    // epoch the delta stake activates
    u64_be get_delta_epoch() const noexcept
    {
        return StorageVariable<Epochs_t>(
                   state_, address_, key_ + Offsets::epochs)
            .load()
            .delta_epoch;
    }

    // epoch the next delta stake activates
    u64_be get_next_delta_epoch() const noexcept
    {
        return StorageVariable<Epochs_t>(
                   state_, address_, key_ + Offsets::epochs)
            .load()
            .next_delta_epoch;
    }

    // the total stake that will come online next epoch.
    uint256_t get_next_epoch_stake() const noexcept
    {
        uint256_t const stake =
            StorageVariable<Stake_t>(state_, address_, key_ + Offsets::stake)
                .load()
                .native();
        uint256_t const delta_stake =
            StorageVariable<DeltaStake_t>(
                state_, address_, key_ + Offsets::delta_stake)
                .load()
                .native();
        uint256_t const next_delta_stake =
            StorageVariable<NextDeltaStake_t>(
                state_, address_, key_ + Offsets::next_delta_stake)
                .load()
                .native();
        return stake + delta_stake + next_delta_stake;
    }

    // set the epoch the delegation (before the epoch delay) will be come
    // active.
    void set_delta_epoch(u64_be const delta_epoch) noexcept
    {
        auto e = epochs().load();
        e.delta_epoch = delta_epoch;
        epochs().store(e);
    }

    // set the epoch the delegation (after the epoch delay) will be come active.
    void set_next_delta_epoch(u64_be const next_delta_epoch) noexcept
    {
        auto e = epochs().load();
        e.next_delta_epoch = next_delta_epoch;
        epochs().store(e);
    }
};

MONAD_STAKING_NAMESPACE_END
