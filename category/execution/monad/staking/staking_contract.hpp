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
#include <category/execution/monad/staking/util/consensus_view.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/execution/monad/staking/util/delegator.hpp>
#include <category/execution/monad/staking/util/staking_error.hpp>
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

        // mapping(uint64 => uint256) consensus_view
        //
        // A view of the execution stake and commmission at the time of the
        // snapshot. This is only set if the validator has a top N stake. Does
        // not account for boundary block.
        ConsensusView consensus_view(u64_be const id) noexcept
        {
            struct
            {
                uint8_t ns;
                u64_be val_id;
                uint8_t slots[23];
            } key{.ns = NSConsensusStake, .val_id = id, .slots = {}};

            return {state_, STAKING_CA, std::bit_cast<bytes32_t>(key)};
        }

        // mapping(uint64 => uint256) snapshot_view
        //
        // A view of the consensus stake and commission at the time of the
        // snapshot.  Referenced by reward during the boundary period.
        SnapshotView snapshot_view(u64_be const id) noexcept
        {
            struct
            {
                uint8_t ns;
                u64_be val_id;
                uint8_t slots[23];
            } key{.ns = NSSnapshotStake, .val_id = id, .slots = {}};

            return {state_, STAKING_CA, std::bit_cast<bytes32_t>(key)};
        }

        // mapping(uint64 => uint256) this_epoch_view
        //
        // A higher level API for getting a view of a validator's stake and
        // commission for this epoch.  Abstracts the boundary block handling
        // from the caller.  The consensus stakes and snapshot stakes are
        // unstable during an epoch, and this function provides a stable
        // interface.
        ConsensusView this_epoch_view(u64_be const id) noexcept
        {
            return in_epoch_delay_period.load_checked().has_value()
                       ? snapshot_view(id)
                       : consensus_view(id);
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

    // The three functions below are mappings with potentially unbounded length.
    // Since precompiles don't have a great way of quantifying gas usage, these
    // functions open up a possible DoS vector. Namely, execution memory usage
    // could be unbounded. To prevent this, both functions will, at most, read
    // `PAGINATED_RESULTS_SIZE` in a single call. The return types in this call
    // are defined by these pagination limits.
    std::tuple<bool, u32_be, std::vector<u64_be>> get_valset(
        StorageArray<u64_be> const &valset, uint32_t const start_index,
        uint32_t limit);

    // The two lists are of Type LinkedList[T] where T = Address | u64_be.  The
    // return type is defined by the pagination:
    // return_type = [bool (done), T (next_in_list), List[T] (results)]
    //
    // When done is set to false, the user may query RPC again starting at
    // `next_in_list`.

    // Gets all the delegators mapped to a validator by following a linked list
    // of addresses in the `Delegator` struct.
    //
    // To start querying from the first delegator, pass in the empty Address (20
    // zero bytes). After that, the `next_in_list` in the output should be used
    // in followup queries until `done` is true.
    std::tuple<bool, Address, std::vector<Address>>
    get_delegators_for_validator(
        u64_be val_id, Address const &start_delegator, uint32_t limit);

    // Gets all the validators that `delegator` is delegated with by following a
    // linked list of validator Ids in the `Delegator` struct.
    //
    // To start querying from the first validator, pass in the empty validator
    // ID (8 zero bytes). After that, the `next_in_list` in the output should be
    // used in followup queries until `done` is true.
    std::tuple<bool, u64_be, std::vector<u64_be>> get_validators_for_delegator(
        Address const &delegator, u64_be start_val_id, uint32_t limit);

private:
    /////////////
    // Events //
    /////////////

    // event ValidatorCreated(
    //     uint64  indexed valId,
    //     address indexed auth_delegator);
    void
    emit_validator_created_event(u64_be val_id, Address const &auth_delegator);

    // event ValidatorStatusChanged(
    //     uint64  indexed valId,
    //     address indexed auth_delegator,
    //     uint64          flags);
    void emit_validator_status_changed_event(u64_be val_id, u64_be flags);

    // event Delegate(
    //     uint64  indexed valId,
    //     address indexed delegator,
    //     uint256         amount,
    //     uint64          activationEpoch);
    void emit_delegation_event(
        u64_be val_id, Address const &delegator, u256_be const &amount,
        u64_be activation_epoch);

    // event Undelegate(
    //      uint64  indexed valId,
    //      address indexed delegator,
    //      uint8           withdrawal_id,
    //      uint256         amount,
    //      uint64          activationEpoch);
    void emit_undelegate_event(
        u64_be val_id, Address const &delegator, uint8_t withdrawal_id,
        u256_be const &amount, u64_be activation_epoch);

    // event Withdraw(
    //      uint64  indexed valId,
    //      address indexed delegator,
    //      uint8           withdrawal_id,
    //      uint256         amount,
    //      uint64          withdrawEpoch);
    void emit_withdraw_event(
        u64_be val_id, Address const &delegator, uint8_t withdrawal_id,
        u256_be const &amount);

    // event ClaimRewards(
    // uint64  indexed valId,
    // address indexed delegatorAddress
    // uint256         amount);
    void emit_claim_rewards_event(
        u64_be val_id, Address const &delegator, u256_be const &amount);

    // event CommissionChanged(
    // uint64  indexed valId,
    // uint256         oldCommission
    // uint256         newCommission);
    void emit_commission_changed_event(
        u64_be, u256_be const &old_commission, u256_be const &new_commission);

    /////////////
    // Helpers //
    /////////////

    // Mint tokens in the staking contract. Done in reward.
    void mint_tokens(uint256_t const &);

    // Send tokens from the staking contract to a delegator. Done in claim and
    // withdraw.
    void send_tokens(Address const &, uint256_t const &);

    // Sets an existence bit in state that `val_id` is present in the set.
    // Returns `true` if the validator is already in the set. Called in
    // delegate.
    bool add_to_valset(u64_be const val_id);

    // Removes the existence bit. Called in the snapshot syscall.
    void remove_from_valset(u64_be const val_id);

    Result<void> reward_invariant(ValExecution &, uint256_t const &);

    // increments a future accumulator value for a validator.  this value is
    // overriden on epoch change when the accumulator for that epoch is
    // complete. Used by delegate and undelegate.
    void increment_accumulator_refcount(u64_be const val_id);

    // reads an future accumulator from state and decrements the refcount.
    u256_be decrement_accumulator_refcount(u64_be epoch, u64_be const val_id);

    // Returns the epoch when the delegation or undelegation will activate.
    uint64_t get_activation_epoch() const noexcept;

    // Checks if a delegation or undelegation are ready
    bool is_epoch_active(uint64_t) const noexcept;

    // Compounds a delegation into the current stake and computes the rewards
    // for the time that stake was active, then folds that stake in the active
    // delegator stake.
    Result<uint256_t> apply_compound(u64_be, Delegator &);

    // Compounds delegations before and after the boundary, and computes the
    // rewards over those windows. The deltas are then folded into the active
    // stake.
    Result<void> pull_delegator_up_to_date(u64_be, Delegator &);

    // Updates a validator's additive accumulator with the new reward, which
    // goes to every active delegator in the pool.
    Result<void> apply_reward(
        ValExecution &, uint256_t const &reward, uint256_t const &active_stake);

    // helper function for delegate. used by three compiles:
    //  1. add_validator
    //  2. delegate
    //  1. compound
    Result<void> delegate(u64_be, uint256_t const &, Address const &);

    // Helper function for getting a valset. used by the three valset getters.
    Result<byte_string>
    get_valset(byte_string_view, StorageArray<u64_be> const &);

    // Low level helpers for validator and delegator lists
    template <typename Key, typename Ptr>
    Result<void> linked_list_insert(Key const &, Ptr const &);
    template <typename Key, typename Ptr>
    void linked_list_remove(Key const &, Ptr const &);
    template <typename Key, typename Ptr>
    std::tuple<bool, Ptr, std::vector<Ptr>>
    linked_list_traverse(Key const &, Ptr const &, uint32_t limit);

public:
    using PrecompileFunc = Result<byte_string> (StakingContract::*)(
        byte_string_view, evmc_address const &, evmc_bytes32 const &);

    /////////////////
    // Precompiles //
    /////////////////
    static std::pair<PrecompileFunc, uint64_t>
    precompile_dispatch(byte_string_view &);

    Result<byte_string> precompile_get_validator(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Result<byte_string> precompile_get_delegator(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Result<byte_string> precompile_get_withdrawal_request(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Result<byte_string> precompile_get_consensus_valset(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Result<byte_string> precompile_get_snapshot_valset(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Result<byte_string> precompile_get_execution_valset(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Result<byte_string> precompile_get_delegations(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Result<byte_string> precompile_get_delegators(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Result<byte_string> precompile_get_epoch(
        byte_string_view, evmc_address const &, evmc_uint256be const &);

    Result<byte_string> precompile_fallback(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Result<byte_string> precompile_add_validator(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Result<byte_string> precompile_delegate(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Result<byte_string> precompile_undelegate(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Result<byte_string> precompile_compound(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Result<byte_string> precompile_withdraw(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Result<byte_string> precompile_claim_rewards(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Result<byte_string> precompile_change_commission(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Result<byte_string> precompile_external_reward(
        byte_string_view, evmc_address const &, evmc_uint256be const &);

    ////////////////////
    //  System Calls  //
    ////////////////////
    Result<void> syscall_on_epoch_change(byte_string_view);
    Result<void> syscall_reward(byte_string_view, uint256_t const &);
    Result<void> syscall_snapshot(byte_string_view);
};

MONAD_STAKING_NAMESPACE_END
