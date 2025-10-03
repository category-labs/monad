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

#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/monad/staking/fuzzer/staking_contract_model.hpp>
#include <category/vm/evm/explicit_traits.hpp>

namespace
{
    using namespace monad;

    Result<u64_be> decode_u64_be_result(Result<byte_string> &&res)
    {
        BOOST_OUTCOME_TRY(auto const output, std::move(res));
        MONAD_ASSERT(output.size() == 32);
        u64_be x;
        std::memcpy(x.bytes, output.data() + 24, 8);
        return x;
    }

    Result<void> decode_true_result(Result<byte_string> &&res)
    {
        BOOST_OUTCOME_TRY(auto const output, std::move(res));
        MONAD_ASSERT(output.size() == 32);
        MONAD_ASSERT(output[31] == 1);
        return outcome::success();
    }
}

namespace monad::staking::test
{
    StakingContractModel::StakingContractModel()
    {
        trie_db_.commit(
            StateDeltas{
                {STAKING_CA,
                 StateDelta{
                     .account =
                         {std::nullopt, Account{.balance = 0, .nonce = 1}}}}},
            Code{},
            NULL_HASH_BLAKE3,
            BlockHeader{},
            {},
            {},
            {},
            {},
            {},
            {});
        trie_db_.finalize(0, NULL_HASH_BLAKE3);
        trie_db_.set_block_and_prefix(0);

        state_.add_to_balance(STAKING_CA, 0); // create account like a txn would
    }

    uint256_t StakingContractModel::balance_of(Address const &a)
    {
        return intx::be::load<uint256_t>(
            state_.get_current_balance_pessimistic(a));
    }

    std::unordered_set<uint8_t> const &
    StakingContractModel::active_withdrawal_ids(u64_be v, Address const &a)
    {
        return delegator_to_active_withdrawal_ids_[{v.native(), a}];
    }

    uint256_t
    StakingContractModel::unit_bias_rewards(u64_be v, Address const &a)
    {
        return unit_bias_rewards_[{v.native(), a}];
    }

    uint256_t
    StakingContractModel::delegator_stake(u64_be v, Address const &a, u64_be e)
    {
        return get_delegator_stake(v.native(), a, e.native());
    }

    uint256_t
    StakingContractModel::withdrawal_stake(u64_be v, Address const &a, u64_be e)
    {
        return get_withdrawal_stake(v.native(), a, e.native());
    }

    uint256_t StakingContractModel::active_consensus_commission(u64_be val_id)
    {
        return active_consensus_commission_[val_id.native()];
    }

    uint256_t StakingContractModel::active_consensus_stake(u64_be val_id)
    {
        return active_consensus_stake_[val_id.native()];
    }

    uint256_t StakingContractModel::error_bound()
    {
        return error_bound_;
    }

    StakingContract::RefCountedAccumulator
    StakingContractModel::accumulated_reward_per_token(
        u64_be epoch, u64_be val_id)
    {
        return contract_.vars.accumulated_reward_per_token(epoch, val_id)
            .load();
    }

    uint256_t StakingContractModel::live_accumulated_reward_per_token(
        u64_be epoch, u64_be val_id)
    {
        if (contract_.vars.epoch.load().native() < epoch.native()) {
            return contract_.vars.val_execution(val_id)
                .accumulated_reward_per_token()
                .load()
                .native();
        }
        return contract_.vars.accumulated_reward_per_token(epoch, val_id)
            .load()
            .value.native();
    }

    bool StakingContractModel::in_epoch_delay_period()
    {
        return contract_.vars.in_epoch_delay_period.load_checked().has_value();
    }

    uint64_t StakingContractModel::last_val_id()
    {
        return contract_.vars.last_val_id.load().native();
    }

    uint64_t StakingContractModel::epoch()
    {
        return contract_.vars.epoch.load().native();
    }

    uint64_t StakingContractModel::val_id(Address const &a)
    {
        return contract_.vars.val_id(a).load().native();
    }

    uint64_t StakingContractModel::val_id_bls(Address const &a)
    {
        return contract_.vars.val_id_bls(a).load().native();
    }

    ValExecution StakingContractModel::val_execution(u64_be v)
    {
        return contract_.vars.val_execution(v);
    }

    StorageVariable<StakingContract::WithdrawalRequest>
    StakingContractModel::withdrawal_request(
        u64_be val_id, Address const &delegator, u8_be wid)
    {
        return contract_.vars.withdrawal_request(val_id, delegator, wid);
    }

    Delegator StakingContractModel::delegator(u64_be v, Address const &a)
    {
        return contract_.vars.delegator(v, a);
    }

    StorageArray<u64_be> StakingContractModel::valset_execution()
    {
        return contract_.vars.valset_execution;
    }

    StorageArray<u64_be> StakingContractModel::valset_snapshot()
    {
        return contract_.vars.valset_snapshot;
    }

    StorageArray<u64_be> StakingContractModel::valset_consensus()
    {
        return contract_.vars.valset_consensus;
    }

    ConsensusView StakingContractModel::consensus_view(u64_be v)
    {
        return contract_.vars.consensus_view(v);
    }

    ConsensusView StakingContractModel::snapshot_view(u64_be v)
    {
        return contract_.vars.snapshot_view(v);
    }

    StorageVariable<u256_be> StakingContractModel::val_bitset_bucket(u64_be v)
    {
        return contract_.vars.val_bitset_bucket(v);
    }

    std::vector<Address>
    StakingContractModel::get_delegators_for_validator(u64_be val_id)
    {
        auto const [done, _, ds] = contract_.get_delegators_for_validator(
            val_id, Address{}, std::numeric_limits<uint32_t>::max());
        MONAD_ASSERT(done);
        return ds;
    }

    std::vector<u64_be>
    StakingContractModel::get_validators_for_delegator(Address const &addr)
    {
        auto const [done, _, vs] = contract_.get_validators_for_delegator(
            addr, 0, std::numeric_limits<uint32_t>::max());
        MONAD_ASSERT(done);
        return vs;
    }

    uint256_t StakingContractModel::calculate_rewards(
        uint256_t const &x, uint256_t const &q, uint256_t const &p)
    {
        return (x * (q - p)) / UNIT_BIAS;
    }

    uint256_t StakingContractModel::withdrawal_reward(
        u64_be val_id, Address const &addr, u8_be id)
    {
        auto withdraw =
            contract_.vars.withdrawal_request(val_id, addr, id).load();
        if (withdraw.epoch.native() == 0) {
            return 0;
        }
        auto const x = withdraw.amount.native();
        auto const q =
            live_accumulated_reward_per_token(withdraw.epoch, val_id);
        auto const p = withdraw.acc.native();
        MONAD_ASSERT(q >= p);
        return calculate_rewards(x, q, p);
    }

    uint256_t
    StakingContractModel::unaccumulated_rewards(u64_be v, evmc_address const &a)
    {
        auto del = contract_.vars.delegator(v, a);
        auto const epoch = contract_.vars.epoch.load().native();
        auto const delta_epoch = del.get_delta_epoch();
        auto const next_delta_epoch = del.get_next_delta_epoch();

        auto const t1 = del.stake().load().native();
        auto const p1 = del.accumulated_reward_per_token().load().native();
        auto const d1 =
            contract_.vars.accumulated_reward_per_token(delta_epoch, v)
                .load()
                .value.native();
        uint256_t q1 = p1;
        if (delta_epoch.native() != 0 && delta_epoch.native() <= epoch) {
            q1 = d1;
        }
        MONAD_ASSERT(q1 >= p1);
        auto const r1 = calculate_rewards(t1, q1, p1);

        auto t2 = t1;
        if (delta_epoch.native() <= epoch) {
            t2 += del.delta_stake().load().native();
        }
        auto const p2 = q1;
        auto const d2 =
            contract_.vars.accumulated_reward_per_token(next_delta_epoch, v)
                .load()
                .value.native();
        auto q2 = p2;
        if (next_delta_epoch.native() != 0 &&
            next_delta_epoch.native() <= epoch) {
            q2 = d2;
        }
        MONAD_ASSERT(q2 >= p2);
        auto const r2 = calculate_rewards(t2, q2, p2);

        auto t3 = t2;
        if (next_delta_epoch.native() <= epoch) {
            t3 += del.next_delta_stake().load().native();
        }
        auto const p3 = q2;
        auto val = contract_.vars.val_execution(v);
        auto const q3 = val.accumulated_reward_per_token().load().native();
        MONAD_ASSERT(q3 >= p3);
        auto const r3 = calculate_rewards(t3, q3, p3);

        return r1 + r2 + r3;
    }

    uint256_t
    StakingContractModel::pending_rewards(u64_be v, evmc_address const &a)
    {
        uint256_t sum{};
        auto const &is = delegator_to_active_withdrawal_ids_[{v.native(), a}];
        for (uint8_t const i : is) {
            sum += withdrawal_reward(v, a, i);
        }
        return sum + unaccumulated_rewards(v, a);
    }

    Result<void>
    StakingContractModel::syscall_on_epoch_change(u64_be next_epoch)
    {
        auto const input = abi_encode_uint(next_epoch);
        pre_call(evmc_uint256be{});
        auto res = contract_.syscall_on_epoch_change(input, 0);
        post_call(res);
        if (res.has_value()) {
            active_consensus_stake_.clear();
            active_consensus_commission_.clear();
            auto valset_consensus = contract_.vars.valset_consensus;
            uint64_t const n = valset_consensus.length();
            for (uint64_t i = 0; i < n; ++i) {
                u64_be const val_id = valset_consensus.get(i).load();
                auto consensus_view = contract_.vars.consensus_view(val_id);
                active_consensus_stake_[val_id.native()] =
                    consensus_view.stake().load().native();
                active_consensus_commission_[val_id.native()] =
                    consensus_view.commission().load().native();
            }
        }
        return res;
    }

    Result<void> StakingContractModel::syscall_snapshot()
    {
        pre_call(evmc_uint256be{});
        auto res = contract_.syscall_snapshot({}, 0);
        post_call(res);
        return res;
    }

    template <Traits traits>
    Result<void> StakingContractModel::syscall_reward(
        Address const &addr, u256_be const &reward)
    {
        auto const input = abi_encode_address(addr);
        pre_call(evmc_uint256be{});
        auto res = contract_.syscall_reward<traits>(input, reward.native());
        post_call(res);
        if (res.has_value()) {
            u64_be v = contract_.vars.val_id(addr).load();
            auto const p = active_consensus_commission_[v.native()];
            auto const c = (reward.native() * p) / MON;
            auto const a = contract_.vars.val_execution(v).auth_address();
            unit_bias_rewards_[{v.native(), a}] += c * UNIT_BIAS;
            distribute_reward(v, u256_be{reward.native() - c});
            error_bound_ += 1;
        }
        return res;
    }

    EXPLICIT_MONAD_TRAITS_MEMBER(StakingContractModel::syscall_reward)

    template <Traits traits>
    Result<u64_be> StakingContractModel::precompile_add_validator(
        byte_string_view message, byte_string_view secp_signature,
        byte_string_view bls_signature, evmc_address const &sender,
        evmc_uint256be const &value)
    {
        AbiEncoder encoder;
        encoder.add_uint<u32_be>(
            abi_encode_selector("addValidator(bytes,bytes,bytes)"));
        encoder.add_bytes(message);
        encoder.add_bytes(secp_signature);
        encoder.add_bytes(bls_signature);
        auto const input = encoder.encode_final();

        auto res = dispatch<traits>(input, sender, value);
        BOOST_OUTCOME_TRY(
            auto const val_id, decode_u64_be_result(std::move(res)));

        byte_string_view reader{message};
        reader.remove_prefix(81);
        auto const addr =
            unaligned_load<Address>(reader.substr(0, sizeof(Address)).data());

        auto const epoch = contract_.vars.in_epoch_delay_period.load()
                               ? contract_.vars.epoch.load().native() + 2
                               : contract_.vars.epoch.load().native() + 1;

        add_delegator_stake(
            val_id.native(),
            addr,
            epoch,
            intx::be::load<uint256_t>(value.bytes));

        val_id_to_historic_delegators_[val_id.native()].insert(addr);

        return val_id;
    }

    EXPLICIT_MONAD_TRAITS_MEMBER(StakingContractModel::precompile_add_validator)

    template <Traits traits>
    Result<void> StakingContractModel::precompile_delegate(
        u64_be val_id, evmc_address const &sender, evmc_uint256be const &value)
    {
        AbiEncoder encoder;
        encoder.add_uint<u32_be>(abi_encode_selector("delegate(uint64)"));
        encoder.add_uint<u64_be>(val_id);
        auto const input = encoder.encode_final();

        auto res = dispatch<traits>(input, sender, value);
        BOOST_OUTCOME_TRY(decode_true_result(std::move(res)));

        auto const epoch = contract_.vars.in_epoch_delay_period.load()
                               ? contract_.vars.epoch.load().native() + 2
                               : contract_.vars.epoch.load().native() + 1;

        add_delegator_stake(
            val_id.native(),
            sender,
            epoch,
            intx::be::load<uint256_t>(value.bytes));

        val_id_to_historic_delegators_[val_id.native()].insert(sender);

        error_bound_ += 3;

        return outcome::success();
    }

    EXPLICIT_MONAD_TRAITS_MEMBER(StakingContractModel::precompile_delegate)

    template <Traits traits>
    Result<void> StakingContractModel::precompile_undelegate(
        u64_be val_id, u256_be const &stake, u8_be withdrawal_id,
        evmc_address const &sender, evmc_uint256be const &value)
    {
        AbiEncoder encoder;
        encoder.add_uint<u32_be>(
            abi_encode_selector("undelegate(uint64,uint256,uint8)"));
        encoder.add_uint(val_id);
        encoder.add_uint(stake);
        encoder.add_uint(withdrawal_id);
        auto const input = encoder.encode_final();

        auto res = dispatch<traits>(input, sender, value);
        BOOST_OUTCOME_TRY(decode_true_result(std::move(res)));

        auto const this_epoch = contract_.vars.epoch.load().native();

        auto const before =
            get_delegator_stake(val_id.native(), sender, this_epoch);
        auto const effective_undel =
            before - stake.native() >= limits::dust_threshold() ? stake.native()
                                                                : before;

        add_delegator_stake(
            val_id.native(), sender, this_epoch, -effective_undel);

        auto const end_epoch = contract_.vars.in_epoch_delay_period.load()
                                   ? this_epoch + 2
                                   : this_epoch + 1;

        add_withdrawal_stake(
            val_id.native(), sender, end_epoch, effective_undel);

        if (effective_undel > 0) {
            delegator_to_active_withdrawal_ids_[{val_id.native(), sender}]
                .insert(withdrawal_id.native());
        }

        error_bound_ += 3;

        return outcome::success();
    }

    EXPLICIT_MONAD_TRAITS_MEMBER(StakingContractModel::precompile_undelegate)

    template <Traits traits>
    Result<void> StakingContractModel::precompile_compound(
        u64_be val_id, evmc_address const &sender, evmc_uint256be const &value)
    {
        auto const stake =
            unaccumulated_rewards(val_id, sender) +
            contract_.vars.delegator(val_id, sender).rewards().load().native();

        AbiEncoder encoder;
        encoder.add_uint<u32_be>(abi_encode_selector("compound(uint64)"));
        encoder.add_uint<u64_be>(val_id);
        auto const input = encoder.encode_final();
        auto res = dispatch<traits>(input, sender, value);
        BOOST_OUTCOME_TRY(decode_true_result(std::move(res)));

        unit_bias_rewards_[{val_id.native(), sender}] -= stake * UNIT_BIAS;

        auto const epoch = contract_.vars.in_epoch_delay_period.load()
                               ? contract_.vars.epoch.load().native() + 2
                               : contract_.vars.epoch.load().native() + 1;

        add_delegator_stake(val_id.native(), sender, epoch, stake);

        error_bound_ += 3;

        return outcome::success();
    }

    EXPLICIT_MONAD_TRAITS_MEMBER(StakingContractModel::precompile_compound)

    template <Traits traits>
    Result<void> StakingContractModel::precompile_withdraw(
        u64_be val_id, u8_be withdrawal_id, evmc_address const &sender,
        evmc_uint256be const &value)
    {
        auto const reward = withdrawal_reward(val_id, sender, withdrawal_id);

        AbiEncoder encoder;
        encoder.add_uint<u32_be>(abi_encode_selector("withdraw(uint64,uint8)"));
        encoder.add_uint(val_id);
        encoder.add_uint(withdrawal_id);
        auto const input = encoder.encode_final();
        auto res = dispatch<traits>(input, sender, value);
        if (res.has_value()) {
            error_bound_ += 1;
            unit_bias_rewards_[{val_id.native(), sender}] -= reward * UNIT_BIAS;
            delegator_to_active_withdrawal_ids_[{val_id.native(), sender}]
                .erase(withdrawal_id.native());
        }
        return decode_true_result(std::move(res));
    }

    EXPLICIT_MONAD_TRAITS_MEMBER(StakingContractModel::precompile_withdraw)

    template <Traits traits>
    Result<void> StakingContractModel::precompile_claim_rewards(
        u64_be val_id, evmc_address const &sender, evmc_uint256be const &value)
    {
        auto const stake =
            unaccumulated_rewards(val_id, sender) +
            contract_.vars.delegator(val_id, sender).rewards().load().native();

        AbiEncoder encoder;
        encoder.add_uint<u32_be>(abi_encode_selector("claimRewards(uint64)"));
        encoder.add_uint<u64_be>(val_id);
        auto const input = encoder.encode_final();
        auto res = dispatch<traits>(input, sender, value);
        if (res.has_value()) {
            error_bound_ += 3;
            unit_bias_rewards_[{val_id.native(), sender}] -= stake * UNIT_BIAS;
        }
        return decode_true_result(std::move(res));
    }

    EXPLICIT_MONAD_TRAITS_MEMBER(StakingContractModel::precompile_claim_rewards)

    template <Traits traits>
    Result<void> StakingContractModel::precompile_change_commission(
        u64_be val_id, u256_be const &new_commission,
        evmc_address const &sender, evmc_uint256be const &value)
    {
        AbiEncoder encoder;
        encoder.add_uint<u32_be>(
            abi_encode_selector("changeCommission(uint64,uint256)"));
        encoder.add_uint<u64_be>(val_id);
        encoder.add_uint<u256_be>(new_commission);
        auto const input = encoder.encode_final();
        auto res = dispatch<traits>(input, sender, value);
        return decode_true_result(std::move(res));
    }

    EXPLICIT_MONAD_TRAITS_MEMBER(
        StakingContractModel::precompile_change_commission)

    template <Traits traits>
    Result<void> StakingContractModel::precompile_external_reward(
        u64_be val_id, evmc_address const &sender, evmc_uint256be const &value)
    {
        AbiEncoder encoder;
        encoder.add_uint<u32_be>(abi_encode_selector("externalReward(uint64)"));
        encoder.add_uint<u64_be>(val_id);
        auto const input = encoder.encode_final();
        auto res = dispatch<traits>(input, sender, value);
        if (res.has_value()) {
            auto const rew = intx::be::load<uint256_t>(value.bytes);
            distribute_reward(val_id, u256_be{rew});
            error_bound_ += 1;
        }
        return decode_true_result(std::move(res));
    }

    EXPLICIT_MONAD_TRAITS_MEMBER(
        StakingContractModel::precompile_external_reward)

    template <Traits traits>
    Result<void> StakingContractModel::precompile_get_delegator(
        u64_be val_id, Address const &addr, evmc_address const &sender,
        evmc_uint256be const &value)
    {
        AbiEncoder encoder;
        encoder.add_uint<u32_be>(
            abi_encode_selector("getDelegator(uint64,address)"));
        encoder.add_uint<u64_be>(val_id);
        encoder.add_address(addr);
        auto const input = encoder.encode_final();
        BOOST_OUTCOME_TRY(dispatch<traits>(input, sender, value));
        error_bound_ += 3;
        return outcome::success();
    }

    EXPLICIT_MONAD_TRAITS_MEMBER(StakingContractModel::precompile_get_delegator)

    uint256_t StakingContractModel::get_delegator_stake(
        uint64_t val_id, Address const &addr, uint64_t epoch)
    {
        auto const &m = delegator_stake_[{val_id, addr}];
        auto it = m.lower_bound(epoch);
        return it == m.end() ? uint256_t{} : it->second;
    }

    uint256_t StakingContractModel::get_withdrawal_stake(
        uint64_t val_id, Address const &addr, uint64_t epoch)
    {
        return withdrawal_stake_[{val_id, addr, epoch}];
    }

    void StakingContractModel::add_delegator_stake(
        uint64_t val_id, Address const &addr, uint64_t epoch,
        uint256_t const &delta)
    {
        auto &m = delegator_stake_[{val_id, addr}];
        auto const prev = get_delegator_stake(val_id, addr, epoch);
        m[epoch] = prev + delta;
        auto it = m.find(epoch);
        MONAD_VM_ASSERT(it != m.end());
        // Update stake of all elements with key > epoch:
        for (;;) {
            if (it == m.begin()) {
                break;
            }
            --it;
            it->second += delta;
        }
    }

    void StakingContractModel::add_withdrawal_stake(
        uint64_t val_id, Address const &addr, uint64_t end_epoch,
        uint256_t const &delta)
    {
        uint64_t const begin_epoch = contract_.vars.epoch.load().native();
        for (uint64_t e = begin_epoch; e < end_epoch; ++e) {
            withdrawal_stake_[{val_id, addr, e}] += delta;
        }
    }

    void StakingContractModel::distribute_reward(
        u64_be val_id, u256_be const &reward_be)
    {
        auto const v = val_id.native();
        auto const rew = reward_be.native();
        auto const rr = (rew * UNIT_BIAS) / active_consensus_stake_[v];

        auto const &dels = val_id_to_historic_delegators_[v];
        auto const epoch = contract_.vars.epoch.load().native();

        uint256_t computed_total_stake;
        for (auto const &a : dels) {
            auto x = get_delegator_stake(v, a, epoch) +
                     get_withdrawal_stake(v, a, epoch);
            unit_bias_rewards_[{v, a}] += x * rr;
            computed_total_stake += x;
        }
        MONAD_ASSERT(computed_total_stake == active_consensus_stake_[v]);
    }

    void StakingContractModel::pre_call(evmc_uint256be const &value)
    {
        state_.push();
        state_.add_to_balance(
            STAKING_CA, intx::be::load<uint256_t>(value.bytes));
    }

    template <typename T>
    void StakingContractModel::post_call(Result<T> const &res)
    {
        if (res.has_value()) {
            state_.pop_accept();
        }
        else {
            state_.pop_reject();
        }
    }

    template <Traits traits>
    Result<byte_string> StakingContractModel::dispatch(
        byte_string const &input, evmc_address const &sender,
        evmc_uint256be const &value)
    {
        pre_call(value);
        byte_string_view msg_input(input);
        msg_input.remove_prefix(28);
        auto [f, _] = contract_.precompile_dispatch<traits>(msg_input);
        auto res = (contract_.*f)(msg_input, (sender), (value));
        post_call(res);
        return res;
    }

    EXPLICIT_MONAD_TRAITS_MEMBER(StakingContractModel::dispatch)
}
