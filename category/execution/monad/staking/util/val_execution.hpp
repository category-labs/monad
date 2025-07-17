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

///////////////////
// Compact slots //
///////////////////
struct KeysPacked
{
    byte_string_fixed<33> secp_pubkey;
    byte_string_fixed<48> bls_pubkey;
};

static_assert(StorageVariable<KeysPacked>::N == 3);

struct AddressFlags
{
    Address auth_address;
    u64_be flags;
};

static_assert(StorageVariable<AddressFlags>::N == 1);

// ValExecution is execution's view of all the validator metadata. All updates
// to validator state are applied to this struct in state immediately after
// performing a contract action.
class ValExecution
{
    State &state_;
    Address const &address_;
    uint256_t const key_;

public:
    ////////////
    // Layout //
    ////////////
    using Stake_t = u256_be;
    using RewardsPerToken_t = u256_be;
    using Commission_t = u256_be;
    using Keys_t = KeysPacked;
    using AddressFlags_t = AddressFlags;
    using UnclaimedRewards_t = u256_be;

    struct Offsets
    {
        static constexpr size_t stake = 0;
        static constexpr size_t rewards_per_token =
            stake + StorageVariable<Stake_t>::N;
        static constexpr size_t commission =
            rewards_per_token + StorageVariable<RewardsPerToken_t>::N;
        static constexpr size_t keys =
            commission + StorageVariable<Commission_t>::N;
        static constexpr size_t address_flags =
            keys + StorageVariable<Keys_t>::N;
        static constexpr size_t unclaimed_rewards =
            address_flags + StorageVariable<AddressFlags_t>::N;
    };

    ValExecution(State &state, Address const &address, bytes32_t const key);

    /////////////
    // Getters //
    /////////////

    // Total stake in the validator pool
    auto stake() noexcept
    {
        return StorageVariable<Stake_t>(
            state_, address_, key_ + Offsets::stake);
    }

    // Validator's rewards per token. This is updated on every call to reward()
    auto accumulated_reward_per_token() noexcept
    {
        return StorageVariable<RewardsPerToken_t>(
            state_, address_, key_ + Offsets::rewards_per_token);
    }

    // Immutable: validator commission rate. Valid values are [0,1e18]
    auto commission() noexcept
    {
        return StorageVariable<Commission_t>(
            state_, address_, key_ + Offsets::commission);
    }

    // Immutable: Bls and Secp keys the validator signs blocks with
    auto keys() noexcept
    {
        return StorageVariable<Keys_t>{state_, address_, key_ + Offsets::keys};
    }

    // Auth address and flags packed into a single slot. See the helpers for
    // getting these individually.
    auto address_flags() noexcept
    {
        return StorageVariable<AddressFlags_t>{
            state_, address_, key_ + Offsets::address_flags};
    }

    // Unclaimed rewards in the validator pool. Used for internal solvency
    // checks so that a delegator cannot realize more rewards available to the
    // pool.
    auto unclaimed_rewards() noexcept
    {
        return StorageVariable<UnclaimedRewards_t>{
            state_, address_, key_ + Offsets::unclaimed_rewards};
    }

    /////////////
    // Helpers //
    /////////////

    // Auth account used to create the validator
    Address auth_address() const noexcept
    {
        return StorageVariable<AddressFlags_t>{
            state_, address_, key_ + Offsets::address_flags}
            .load()
            .auth_address;
    }

    // Flags indicating validators state. Any nonzero value implies the
    // validator is not a candidate for the consensus set next epoch.
    uint64_t get_flags() const noexcept
    {
        return StorageVariable<AddressFlags_t>{
            state_, address_, key_ + Offsets::address_flags}
            .load()
            .flags.native();
    }

    void set_flag(uint64_t const flag) noexcept
    {
        auto af = address_flags().load();
        af.flags = af.flags.native() | flag;
        address_flags().store(af);
    }

    void clear_flag(uint64_t const flag) noexcept
    {
        auto af = address_flags().load();
        af.flags = af.flags.native() & ~flag;
        address_flags().store(af);
    }

    bool exists() const noexcept
    {
        return auth_address() != Address{};
    }
};

MONAD_STAKING_NAMESPACE_END
