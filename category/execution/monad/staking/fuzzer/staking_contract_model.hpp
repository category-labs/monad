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

#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>
#include <category/vm/evm/traits.hpp>

#include <boost/functional/hash.hpp>

namespace monad::staking::test
{
    class StakingContractModel
    {
        vm::VM vm_;
        OnDiskMachine mpt_machine_;
        mpt::Db mpt_db_{mpt_machine_};
        TrieDb trie_db_{mpt_db_};
        BlockState block_state_{trie_db_, vm_};
        State state_{block_state_, Incarnation{0, 0}};
        NoopCallTracer call_tracer_{};
        StakingContract contract_{state_, call_tracer_};

        // An upper bound on reward rounding errors:
        uint256_t error_bound_{};

        using UnitBiasRewardsMap = std::unordered_map<
            std::tuple<uint64_t, Address>, uint256_t,
            boost::hash<std::tuple<uint64_t, Address>>>;

        // unit_bias_rewards[{v, a}] is the sum of rewards distributed to
        // delegator(v, a), but not yet claimed/compounded.
        UnitBiasRewardsMap unit_bias_rewards_;

        using ActiveConsensusStakeMap = std::unordered_map<uint64_t, uint256_t>;

        // The stake of the active consensus validators:
        ActiveConsensusStakeMap active_consensus_stake_;

        using ActiveConsensusCommissionMap = ActiveConsensusStakeMap;

        // The commission rate of the active consensus validators:
        ActiveConsensusCommissionMap active_consensus_commission_;

        using DelegatorStakeMap = std::unordered_map<
            std::tuple<uint64_t, Address>,
            std::map<uint64_t, uint256_t, std::greater<uint64_t>>,
            boost::hash<std::tuple<uint64_t, Address>>>;

        // delegator_stake[{v, a, e}] is the stake of delegator(v, a)
        // in epoch e:
        DelegatorStakeMap delegator_stake_;

        using WithdrawalStakeMap = std::unordered_map<
            std::tuple<uint64_t, Address, uint64_t>, uint256_t,
            boost::hash<std::tuple<uint64_t, Address, uint64_t>>>;

        // withdrawal_stake[{v, a, e}] is the stake of delegator(v, a)
        // in epoch e which has been undelegated, but the stake is eligible
        // for rewards.
        WithdrawalStakeMap withdrawal_stake_;

        using ValIdToDelegatorsMap =
            std::unordered_map<uint64_t, std::unordered_set<Address>>;

        ValIdToDelegatorsMap val_id_to_historic_delegators_;

        using DelegatorToActiveWithdrawalIdsMap = std::unordered_map<
            std::tuple<uint64_t, Address>, std::unordered_set<uint8_t>,
            boost::hash<std::tuple<uint64_t, Address>>>;

        DelegatorToActiveWithdrawalIdsMap delegator_to_active_withdrawal_ids_;

    public:
        StakingContractModel();

        uint256_t balance_of(Address const &);

        std::unordered_set<uint8_t> const &
        active_withdrawal_ids(u64_be, Address const &);

        uint256_t unit_bias_rewards(u64_be v, Address const &a);

        uint256_t delegator_stake(u64_be, Address const &, u64_be);

        uint256_t withdrawal_stake(u64_be, Address const &, u64_be);

        uint256_t active_consensus_commission(u64_be);

        uint256_t active_consensus_stake(u64_be);

        uint256_t error_bound();

        StakingContract::RefCountedAccumulator
        accumulated_reward_per_token(u64_be epoch, u64_be val_id);

        uint256_t
        live_accumulated_reward_per_token(u64_be epoch, u64_be val_id);

        bool in_epoch_delay_period();

        uint64_t last_val_id();

        uint64_t epoch();

        uint64_t val_id(Address const &);

        uint64_t val_id_bls(Address const &);

        ValExecution val_execution(u64_be);

        Delegator delegator(u64_be, Address const &);

        StorageVariable<StakingContract::WithdrawalRequest>
        withdrawal_request(u64_be, Address const &, u8_be);

        StorageArray<u64_be> valset_execution();

        StorageArray<u64_be> valset_snapshot();

        StorageArray<u64_be> valset_consensus();

        ConsensusView consensus_view(u64_be);

        ConsensusView snapshot_view(u64_be);

        StorageVariable<u256_be> val_bitset_bucket(u64_be);

        std::vector<Address> get_delegators_for_validator(u64_be);

        std::vector<u64_be> get_validators_for_delegator(Address const &);

        static uint256_t calculate_rewards(
            uint256_t const &, uint256_t const &, uint256_t const &);

        uint256_t withdrawal_reward(u64_be, Address const &, u8_be);

        uint256_t unaccumulated_rewards(u64_be, evmc_address const &);

        uint256_t pending_rewards(u64_be, evmc_address const &);

        Result<void> syscall_on_epoch_change(u64_be);

        Result<void> syscall_snapshot();

        template <Traits traits>
        Result<void> syscall_reward(Address const &, u256_be const &);

        template <Traits traits>
        Result<u64_be> precompile_add_validator(
            byte_string_view message, byte_string_view secp_signature,
            byte_string_view bls_signature, evmc_address const &sender,
            evmc_uint256be const &value);

        template <Traits traits>
        Result<void> precompile_delegate(
            u64_be val_id, evmc_address const &sender,
            evmc_uint256be const &value);

        template <Traits traits>
        Result<void> precompile_undelegate(
            u64_be val_id, u256_be const &stake, u8_be withdrawal_id,
            evmc_address const &sender, evmc_uint256be const &value);

        template <Traits traits>
        Result<void> precompile_compound(
            u64_be val_id, evmc_address const &sender,
            evmc_uint256be const &value);

        template <Traits traits>
        Result<void> precompile_withdraw(
            u64_be val_id, u8_be withdrawal_id, evmc_address const &sender,
            evmc_uint256be const &value);

        template <Traits traits>
        Result<void> precompile_claim_rewards(
            u64_be val_id, evmc_address const &sender,
            evmc_uint256be const &value);

        template <Traits traits>
        Result<void> precompile_change_commission(
            u64_be val_id, u256_be const &new_commission,
            evmc_address const &sender, evmc_uint256be const &value);

        template <Traits traits>
        Result<void> precompile_external_reward(
            u64_be val_id, evmc_address const &sender,
            evmc_uint256be const &value);

        // Result type is not accurate. Just interested in the side
        // effects of this function on the state:
        template <Traits traits>
        Result<void> precompile_get_delegator(
            u64_be val_id, Address const &addr, evmc_address const &sender,
            evmc_uint256be const &value);

    private:
        uint256_t get_delegator_stake(uint64_t, Address const &, uint64_t);
        uint256_t get_withdrawal_stake(uint64_t, Address const &, uint64_t);
        void add_delegator_stake(
            uint64_t, Address const &, uint64_t, uint256_t const &);
        void add_withdrawal_stake(
            uint64_t, Address const &, uint64_t, uint256_t const &);

        void distribute_reward(u64_be, u256_be const &);

        void pre_call(evmc_uint256be const &value);

        template <typename T>
        void post_call(Result<T> const &);

        template <Traits traits>
        Result<byte_string> dispatch(
            byte_string const &input, evmc_address const &sender,
            evmc_uint256be const &value);
    };
}
