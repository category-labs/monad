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
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/core/contract/storage_array.hpp>
#include <category/execution/ethereum/core/contract/storage_variable.hpp>
#include <category/execution/monad/staking/config.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/execution/monad/staking/util/delegator.hpp>
#include <category/execution/monad/staking/util/val_execution.hpp>

#include <evmc/evmc.h>

#include <cstdint>
#include <optional>
#include <string_view>

MONAD_NAMESPACE_BEGIN

class State;

MONAD_NAMESPACE_END

MONAD_STAKING_NAMESPACE_BEGIN

class StakingContract
{
    State &state_;

public:
    StakingContract(State &);

    struct WithdrawalRequest
    {
        u256_be amount;
        u256_be acc;
        u64_be epoch;
    };

    static_assert(sizeof(WithdrawalRequest) == 72);
    static_assert(alignof(WithdrawalRequest) == 1);

    struct RefCountedAccumulator
    {
        u256_be value;
        u256_be refcount;
    };

    static_assert(sizeof(RefCountedAccumulator) == 64);
    static_assert(alignof(RefCountedAccumulator) == 1);

    /////////////////////////////
    // Staking Storage Variables
    /////////////////////////////
    class Variables
    {
        State &state_;

        // Single slot constants all under namespace 0x0
        static constexpr auto AddressEpoch{
            0x0000000000000000000000000000000000000000000000000000000000000001_bytes32};
        static constexpr auto AddressInBoundary{
            0x0000000000000000000000000000000000000000000000000000000000000002_bytes32};
        static constexpr auto AddressLastValId{
            0x0000000000000000000000000000000000000000000000000000000000000003_bytes32};

        // Working valsets get namespaces 0x1, 0x2, 0x3
        static constexpr auto AddressValsetExecution{
            0x0100000000000000000000000000000000000000000000000000000000000000_bytes32};
        static constexpr auto AddressValsetConsensus{
            0x0200000000000000000000000000000000000000000000000000000000000000_bytes32};
        static constexpr auto AddressValsetSnapshot{
            0x0300000000000000000000000000000000000000000000000000000000000000_bytes32};

        // Namespaces for mappings. Each mapping in the "owns" all the address
        // space under the namespace byte.
        enum Namespace : uint8_t
        {
            NSConsensusStake = 0x04,
            NSSnapshotStake = 0x05,
            NSValIdSecp = 0x06,
            NSValIdBls = 0x07,
            NSValBitset = 0x08,
            NSValExecution = 0x09,
            NSAccumulator = 0x0A,
            NSDelegator = 0x0B,
            NSWithdrawalRequest = 0x0C,
        };

    public:
        explicit Variables(State &state)
            : state_{state}
        {
        }

    public:
        ////////////////
        //  Constants //
        ////////////////

        // The current epoch, which is incremented by syscall_on_epoch_change()
        StorageVariable<u64_be> epoch{state_, STAKING_CA, AddressEpoch};

        // Set to true when consensus has taken a snapshot of the valset for the
        // next epoch. When in the epoch delay period, all delegations and
        // delegations that come after are pushed into the following epoch.
        StorageVariable<bool> in_epoch_delay_period{
            state_, STAKING_CA, AddressInBoundary};

        // Increments everytime a new validator is created. First validator ID
        // is 1.
        StorageVariable<u64_be> last_val_id{
            state_, STAKING_CA, AddressLastValId};

        // Execution valset changes in real time with validator's stake
        StorageArray<u64_be> valset_execution{
            state_, STAKING_CA, AddressValsetExecution};

        // A copy of the execution valset with the top N stake at the snapshot.
        StorageArray<u64_be> valset_consensus{
            state_, STAKING_CA, AddressValsetConsensus};

        // A copy of the consensus valset at the snapshot. This is to continue
        // rewarding validator pools with their same stakes before the boundary.
        StorageArray<u64_be> valset_snapshot{
            state_, STAKING_CA, AddressValsetSnapshot};

        // A higher level API for getting the active valset for this epoch.
        // Abstracts the boundary block handling from the caller. The consensus
        // stakes and snapshot validator sets are unstable during an epoch, and
        // this function provides a stable interface.
        StorageArray<u64_be> this_epoch_valset() noexcept
        {
            return in_epoch_delay_period.load_checked().has_value()
                       ? valset_snapshot
                       : valset_consensus;
        }

        ////////////////
        //  Mappings  //
        ////////////////

        // mapping (address => uint64) val_id
        //
        // Used both for existence and for resolving which validator to reward.
        StorageVariable<u64_be> val_id(Address const &secp_eth_address) noexcept
        {
            struct
            {
                uint8_t ns;
                Address address;
                uint8_t slots[11];
            } key{.ns = NSValIdSecp, .address = secp_eth_address, .slots = {}};

            return {state_, STAKING_CA, std::bit_cast<bytes32_t>(key)};
        }

        // mapping (address => uint64) val_id
        //
        // This mapping only exists to ensure the same bls_key cannot be reused
        // by multiple validators.
        StorageVariable<u64_be>
        val_id_bls(Address const &bls_eth_address) noexcept
        {
            struct
            {
                uint8_t ns;
                Address address;
                uint8_t slots[11];
            } key{.ns = NSValIdBls, .address = bls_eth_address, .slots = {}};

            return {state_, STAKING_CA, std::bit_cast<bytes32_t>(key)};
        }

        // mapping(uint64 => uint256) in_valset_bitset
        //
        // Maps the top 56 bits of a validator to an existence set in state.
        // Existence in the bucket can be determined by using the bottom 8 bits.
        // within the bucket. This is to save storage since 256 val ids can be
        // packed in a single slot.
        StorageVariable<u256_be> val_bitset_bucket(u64_be const val_id) noexcept
        {
            struct
            {
                uint8_t ns;
                u64_be bucket;
                uint8_t slots[23];
            } key{
                .ns = NSValBitset,
                .bucket = (val_id.native() >> 8),
                .slots = {}};

            return {state_, STAKING_CA, std::bit_cast<bytes32_t>(key)};
        }

        // mapping(uint64 => Validator) validator_info
        //
        // A mapping between a validator ID and the validators info. Stake
        // changes are applied to the execution view and copied to the consensus
        // view on snapshot.
        ValExecution val_execution(u64_be const id) noexcept
        {
            struct
            {
                uint8_t ns;
                u64_be val_id;
                uint8_t slots[23];
            } key{.ns = NSValExecution, .val_id = id, .slots = {}};

            return {state_, STAKING_CA, std::bit_cast<bytes32_t>(key)};
        }

        // mapping(uint64 => uint256) consensus_stake
        //
        // A copy of the execution stake at the time of the snapshot. This is
        // only set if the validator has a top N stake. Does not account for
        // boundary block.
        StorageVariable<u256_be> consensus_stake(u64_be const id) noexcept
        {
            struct
            {
                uint8_t ns;
                u64_be val_id;
                uint8_t slots[23];
            } key{.ns = NSConsensusStake, .val_id = id, .slots = {}};

            return {state_, STAKING_CA, std::bit_cast<bytes32_t>(key)};
        }

        // mapping(uint64 => uint256) snapshot_stake
        //
        // A copy of the consensus stake at the time of the snapshot to be
        // referenced by reward during the boundary period.
        StorageVariable<u256_be> snapshot_stake(u64_be const id) noexcept
        {
            struct
            {
                uint8_t ns;
                u64_be val_id;
                uint8_t slots[23];
            } key{.ns = NSSnapshotStake, .val_id = id, .slots = {}};

            return {state_, STAKING_CA, std::bit_cast<bytes32_t>(key)};
        }

        // mapping(uint64 => uint256) this_epoch_stake
        //
        // A higher level API for getting a validator's stake for this epoch.
        // Abstracts the boundary block handling from the caller. The consensus
        // stakes and snapshot stakes are unstable during an epoch, and this
        // function provides a stable interface.
        StorageVariable<u256_be> this_epoch_stake(u64_be const id) noexcept
        {
            return in_epoch_delay_period.load_checked().has_value()
                       ? snapshot_stake(id)
                       : consensus_stake(id);
        }

        // mapping(uint64 => mapping(address => Delegator)) delegator
        //
        // Retrieve a delegators metadata given a validator.
        Delegator
        delegator(u64_be const val_id, Address const &address) noexcept
        {
            struct
            {
                uint8_t ns;
                u64_be val_id;
                Address address;
                uint8_t slots[3];
            } key{
                .ns = NSDelegator,
                .val_id = val_id,
                .address = address,
                .slots = {}};

            return {state_, STAKING_CA, std::bit_cast<bytes32_t>(key)};
        }

        // clang-format off
        // mapping(uint64 => mapping(address => mapping (uint8 => WithdrawalRequest)))
        // clang-format on
        //
        // Retrieves a withdrawal request for a delegator. The user provides the
        // ID during undelegate.
        StorageVariable<WithdrawalRequest> withdrawal_request(
            u64_be const val_id, Address const &delegator,
            uint8_t const withdrawal_id) noexcept
        {
            struct
            {
                uint8_t ns;
                u64_be val_id;
                Address address;
                uint8_t withdrawal_id;
                uint8_t slots[2];
            } key{
                .ns = NSWithdrawalRequest,
                .val_id = val_id,
                .address = delegator,
                .withdrawal_id = withdrawal_id,
                .slots = {}};

            return {state_, STAKING_CA, std::bit_cast<bytes32_t>(key)};
        }

        // mapping(uint64 => mapping(uint64 => bytes32)) acc
        //
        // A future accumulator value representing a validators rewards per
        // token for a given epoch. During delegate/undelegate, a delegator
        // increments the refcount, and this value is applied on epoch change.
        // This accumulator is not made accessible to delegators until that
        // epoch has completed.
        StorageVariable<RefCountedAccumulator> accumulated_reward_per_token(
            u64_be const epoch, u64_be const val_id) noexcept
        {
            struct
            {
                uint8_t ns;
                u64_be epoch;
                u64_be val_id;
                uint8_t slots[15];
            } key{
                .ns = NSAccumulator,
                .epoch = epoch,
                .val_id = val_id,
                .slots = {}};

            return {state_, STAKING_CA, std::bit_cast<bytes32_t>(key)};
        }
    } vars;
};

MONAD_STAKING_NAMESPACE_END
