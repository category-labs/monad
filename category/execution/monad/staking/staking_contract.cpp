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

#include <category/core/byte_string.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/core/monad_exception.hpp>
#include <category/core/unaligned.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/abi_decode.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/contract/checked_math.hpp>
#include <category/execution/ethereum/core/contract/events.hpp>
#include <category/execution/ethereum/core/contract/storage_array.hpp>
#include <category/execution/ethereum/core/contract/storage_variable.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>
#include <category/execution/monad/staking/util/bls.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/execution/monad/staking/util/secp256k1.hpp>
#include <category/execution/monad/system_sender.hpp>

#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>

#include <quill/Quill.h>

#include <algorithm>
#include <cstring>
#include <memory>

MONAD_STAKING_ANONYMOUS_NAMESPACE_BEGIN

////////////////////////
// Function Selectors //
////////////////////////

struct PrecompileSelector
{
    static constexpr uint32_t ADD_VALIDATOR =
        abi_encode_selector("addValidator(bytes,bytes,bytes)");
    static constexpr uint32_t DELEGATE =
        abi_encode_selector("delegate(uint64)");
    static constexpr uint32_t UNDELEGATE =
        abi_encode_selector("undelegate(uint64,uint256,uint8)");
    static constexpr uint32_t COMPOUND =
        abi_encode_selector("compound(uint64)");
    static constexpr uint32_t WITHDRAW =
        abi_encode_selector("withdraw(uint64,uint8)");
    static constexpr uint32_t CLAIM_REWARDS =
        abi_encode_selector("claimRewards(uint64)");
    static constexpr uint32_t CHANGE_COMMISSION =
        abi_encode_selector("changeCommission(uint64,uint256)");
    static constexpr uint32_t EXTERNAL_REWARD =
        abi_encode_selector("externalReward(uint64)");
    static constexpr uint32_t GET_EPOCH = abi_encode_selector("getEpoch()");
    static constexpr uint32_t GET_VALIDATOR =
        abi_encode_selector("getValidator(uint64)");
    static constexpr uint32_t GET_DELEGATOR =
        abi_encode_selector("getDelegator(uint64,address)");
    static constexpr uint32_t GET_WITHDRAWAL_REQUEST =
        abi_encode_selector("getWithdrawalRequest(uint64,address,uint8)");
    static constexpr uint32_t GET_CONSENSUS_VALIDATOR_SET =
        abi_encode_selector("getConsensusValidatorSet(uint32)");
    static constexpr uint32_t GET_SNAPSHOT_VALIDATOR_SET =
        abi_encode_selector("getSnapshotValidatorSet(uint32)");
    static constexpr uint32_t GET_EXECUTION_VALIDATOR_SET =
        abi_encode_selector("getExecutionValidatorSet(uint32)");
    static constexpr uint32_t GET_DELEGATIONS =
        abi_encode_selector("getDelegations(address,uint64)");
    static constexpr uint32_t GET_DELEGATORS =
        abi_encode_selector("getDelegators(uint64,address)");
};

static_assert(PrecompileSelector::ADD_VALIDATOR == 0xf145204c);
static_assert(PrecompileSelector::DELEGATE == 0x84994fec);
static_assert(PrecompileSelector::UNDELEGATE == 0x5cf41514);
static_assert(PrecompileSelector::COMPOUND == 0xb34fea67);
static_assert(PrecompileSelector::WITHDRAW == 0xaed2ee73);
static_assert(PrecompileSelector::CLAIM_REWARDS == 0xa76e2ca5);
static_assert(PrecompileSelector::CHANGE_COMMISSION == 0x9bdcc3c8);
static_assert(PrecompileSelector::EXTERNAL_REWARD == 0xe4b3303b);
static_assert(PrecompileSelector::GET_EPOCH == 0x757991a8);
static_assert(PrecompileSelector::GET_VALIDATOR == 0x2b6d639a);
static_assert(PrecompileSelector::GET_DELEGATOR == 0x573c1ce0);
static_assert(PrecompileSelector::GET_WITHDRAWAL_REQUEST == 0x56fa2045);
static_assert(PrecompileSelector::GET_CONSENSUS_VALIDATOR_SET == 0xfb29b729);
static_assert(PrecompileSelector::GET_SNAPSHOT_VALIDATOR_SET == 0xde66a368);
static_assert(PrecompileSelector::GET_EXECUTION_VALIDATOR_SET == 0x7cb074df);
static_assert(PrecompileSelector::GET_DELEGATIONS == 0x4fd66050);
static_assert(PrecompileSelector::GET_DELEGATORS == 0xa0843a26);

///////////////
// Gas Costs //
///////////////

// The gas for the staking precompile are determined by sloads ,sstores,
// transfers, events and cryptography operations. The operations are given as
// the following:
//
// operations = [
//   number_of_warm_sloads,
//   number_of_cold_sloads,
//   number_of_warm_zero_to_nonzero_sstores,
//   number_of_warm_nonzero_sstores,
//   number_of_cold_zero_to_nonzero_sstores,
//   number_of_events,
//   number_of_transfers,
//   ]
//
// The gas cost is calculated as:
// gas = WARM_SLOAD_COST * operations[0]  +
//       COLD_SLOAD_COST * operations[1] +
//       WARM_ZERO_TO_NONZERO_SSTORE_COST * operations[2] +
//       WARM_NONZERO_SSTORE_COST * operations[3] +
//       COLD_ZERO_TO_NONZERO_SSTORE_COST * operations[4] +
//       EVENT_COST * operations[5] +
//       TRANSFER_COST * operations[6] +
//       cryptography_gas
//

constexpr uint64_t WARM_SLOAD = 100;
constexpr uint64_t COLD_SLOAD = 8100;
constexpr uint64_t WARM_SSTORE = 2900;
constexpr uint64_t WARM_SSTORE_NONZERO = 2900;
constexpr uint64_t COLD_SSTORE = 2900 + 8000;
constexpr uint64_t EVENT_COSTS = 4275;
constexpr uint64_t TRANSFER_COSTS = 11800;
constexpr uint64_t EC_RECOVER_COST = 3000;
constexpr uint64_t BLS_VERIFY_COST = 150000;
constexpr uint64_t MEMORY_EXPANSION_COST = 4000;

struct OpCount
{
    uint64_t warm_sloads;
    uint64_t cold_sloads;
    uint64_t warm_sstores;
    uint64_t warm_sstore_nonzero;
    uint64_t cold_sstores;
    uint64_t events;
    uint64_t transfers;
};

constexpr uint64_t compute_costs(OpCount const &ops)
{
    return WARM_SLOAD * ops.warm_sloads + COLD_SLOAD * ops.cold_sloads +
           WARM_SSTORE * ops.warm_sstores +
           WARM_SSTORE_NONZERO * ops.warm_sstore_nonzero +
           COLD_SSTORE * ops.cold_sstores + EVENT_COSTS * ops.events +
           TRANSFER_COSTS * ops.transfers;
}

constexpr uint64_t ADD_VALIDATOR_OP_COST = compute_costs(OpCount{
                                               .warm_sloads = 21,
                                               .cold_sloads = 22,
                                               .warm_sstores = 6,
                                               .warm_sstore_nonzero = 15,
                                               .cold_sstores = 9,
                                               .events = 3,
                                               .transfers = 0}) +
                                           EC_RECOVER_COST + BLS_VERIFY_COST;

constexpr uint64_t DELEGATE_OP_COST = compute_costs(OpCount{
    .warm_sloads = 21,
    .cold_sloads = 17,
    .warm_sstores = 6,
    .warm_sstore_nonzero = 14,
    .cold_sstores = 5,
    .events = 2,
    .transfers = 0});

constexpr uint64_t UNDELEGATE_OP_COST = compute_costs(OpCount{
    .warm_sloads = 15,
    .cold_sloads = 11,
    .warm_sstores = 8,
    .warm_sstore_nonzero = 5,
    .cold_sstores = 1,
    .events = 2,
    .transfers = 0});

constexpr uint64_t WITHDRAW_OP_COST = compute_costs(OpCount{
    .warm_sloads = 11,
    .cold_sloads = 6,
    .warm_sstores = 1,
    .warm_sstore_nonzero = 0,
    .cold_sstores = 0,
    .events = 1,
    .transfers = 1});

constexpr uint64_t COMPOUND_OP_COST = compute_costs(OpCount{
    .warm_sloads = 46,
    .cold_sloads = 17,
    .warm_sstores = 6,
    .warm_sstore_nonzero = 29,
    .cold_sstores = 3,
    .events = 3,
    .transfers = 0});

constexpr uint64_t CLAIM_REWARDS_OP_COST = compute_costs(OpCount{
    .warm_sloads = 16,
    .cold_sloads = 11,
    .warm_sstores = 2,
    .warm_sstore_nonzero = 11,
    .cold_sstores = 1,
    .events = 1,
    .transfers = 1});

constexpr uint64_t CHANGE_COMMISSION_OP_COST = compute_costs(OpCount{
    .warm_sloads = 0,
    .cold_sloads = 3,
    .warm_sstores = 0,
    .warm_sstore_nonzero = 0,
    .cold_sstores = 1,
    .events = 1,
    .transfers = 0});

constexpr uint64_t EXTERNAL_REWARDS_OP_COST = compute_costs(OpCount{
    .warm_sloads = 0,
    .cold_sloads = 5,
    .warm_sstores = 0,
    .warm_sstore_nonzero = 0,
    .cold_sstores = 2,
    .events = 1,
    .transfers = 0});

constexpr uint64_t GET_EPOCH_OP_COST = compute_costs(OpCount{
    .warm_sloads = 2,
    .cold_sloads = 0,
    .warm_sstores = 0,
    .warm_sstore_nonzero = 0,
    .cold_sstores = 0,
    .events = 0,
    .transfers = 0});

constexpr uint64_t GET_VALIDATOR_OP_COST = compute_costs(OpCount{
    .warm_sloads = 0,
    .cold_sloads = 12,
    .warm_sstores = 0,
    .warm_sstore_nonzero = 0,
    .cold_sstores = 0,
    .events = 0,
    .transfers = 0});

constexpr uint64_t GET_DELEGATOR_OP_COST = compute_costs(OpCount{
    .warm_sloads = 15,
    .cold_sloads = 17,
    .warm_sstores = 1,
    .warm_sstore_nonzero = 11,
    .cold_sstores = 1,
    .events = 0,
    .transfers = 0});

constexpr uint64_t GET_WITHDRAWAL_REQUEST_OP_COST = compute_costs(OpCount{
    .warm_sloads = 0,
    .cold_sloads = 3,
    .warm_sstores = 0,
    .warm_sstore_nonzero = 0,
    .cold_sstores = 0,
    .events = 0,
    .transfers = 0});

constexpr uint64_t GET_VALIDATOR_SET_OP_COST = compute_costs(OpCount{
                                                   .warm_sloads = 0,
                                                   .cold_sloads = 100,
                                                   .warm_sstores = 0,
                                                   .warm_sstore_nonzero = 0,
                                                   .cold_sstores = 0,
                                                   .events = 0,
                                                   .transfers = 0}) +
                                               MEMORY_EXPANSION_COST;

constexpr uint64_t LINKED_LIST_GETTER_OP_COST = compute_costs(OpCount{
                                                    .warm_sloads = 0,
                                                    .cold_sloads = 100,
                                                    .warm_sstores = 0,
                                                    .warm_sstore_nonzero = 0,
                                                    .cold_sstores = 0,
                                                    .events = 0,
                                                    .transfers = 0}) +
                                                MEMORY_EXPANSION_COST;

static_assert(ADD_VALIDATOR_OP_COST == 505125);
static_assert(DELEGATE_OP_COST == 260850);
static_assert(UNDELEGATE_OP_COST == 147750);
static_assert(WITHDRAW_OP_COST == 68675);
static_assert(COMPOUND_OP_COST == 289325);
static_assert(CLAIM_REWARDS_OP_COST == 155375);
static_assert(CHANGE_COMMISSION_OP_COST == 39475);
static_assert(EXTERNAL_REWARDS_OP_COST == 66575);
static_assert(GET_EPOCH_OP_COST == 200);
static_assert(GET_VALIDATOR_OP_COST == 97200);
static_assert(GET_DELEGATOR_OP_COST == 184900);
static_assert(GET_WITHDRAWAL_REQUEST_OP_COST == 24300);
static_assert(GET_VALIDATOR_SET_OP_COST == 814000);
static_assert(LINKED_LIST_GETTER_OP_COST == 814000);

byte_string_view consume_bytes(byte_string_view &data, size_t const num_bytes)
{
    byte_string_view ret = data.substr(0, num_bytes);
    data.remove_prefix(num_bytes);
    return ret;
}

Result<uint256_t>
checked_mul_div(uint256_t const &x, uint256_t const &y, uint256_t const &z)
{
    BOOST_OUTCOME_TRY(auto const p, checked_mul(x, y));
    return checked_div(p, z);
}

Result<uint256_t> calculate_rewards(
    uint256_t const &stake, uint256_t const &current_acc,
    uint256_t const &last_checked_acc)
{
    BOOST_OUTCOME_TRY(
        auto const delta, checked_sub(current_acc, last_checked_acc));
    return checked_mul_div(delta, stake, UNIT_BIAS);
}

Result<void> function_not_payable(evmc_uint256be const &value)
{
    bool const all_zero = std::all_of(
        value.bytes,
        value.bytes + sizeof(evmc_uint256be),
        [](uint8_t const byte) { return byte == 0; });

    if (MONAD_UNLIKELY(!all_zero)) {
        return StakingError::ValueNonZero;
    }
    return outcome::success();
}

MONAD_STAKING_ANONYMOUS_NAMESPACE_END

MONAD_STAKING_NAMESPACE_BEGIN

StakingContract::StakingContract(State &state, CallTracerBase &call_tracer)
    : state_{state}
    , call_tracer_{call_tracer}
    , vars{state}
{
}

/////////////
// Events //
/////////////
void StakingContract::emit_validator_rewarded_event(
    u64_be const val_id, Address const &from, u256_be const &amount)
{
    constexpr bytes32_t signature = abi_encode_event_signature(
        "ValidatorRewarded(uint64,address,uint256,uint64)");
    static_assert(
        signature ==
        0x3a420a01486b6b28d6ae89c51f5c3bde3e0e74eecbb646a0c481ccba3aae3754_bytes32);

    auto const event = EventBuilder(STAKING_CA, signature)
                           .add_topic(abi_encode_uint(val_id))
                           .add_topic(abi_encode_address(from))
                           .add_data(abi_encode_uint(amount))
                           .add_data(abi_encode_uint(vars.epoch.load()))
                           .build();
    emit_log(event);
}

void StakingContract::emit_validator_created_event(
    u64_be const val_id, Address const &auth_delegator,
    u256_be const &commission)

{
    constexpr bytes32_t signature =
        abi_encode_event_signature("ValidatorCreated(uint64,address,uint256)");
    static_assert(
        signature ==
        0x6f8045cd38e512b8f12f6f02947c632e5f25af03aad132890ecf50015d97c1b2_bytes32);

    auto const event = EventBuilder(STAKING_CA, signature)
                           .add_topic(abi_encode_uint(val_id))
                           .add_topic(abi_encode_address(auth_delegator))
                           .add_data(abi_encode_uint(commission))
                           .build();
    emit_log(event);
}

void StakingContract::emit_validator_status_changed_event(
    u64_be const val_id, u64_be const flags)
{
    constexpr bytes32_t signature =
        abi_encode_event_signature("ValidatorStatusChanged(uint64,uint64)");
    static_assert(
        signature ==
        0xc95966754e882e03faffaf164883d98986dda088d09471a35f9e55363daf0c53_bytes32);

    auto const event = EventBuilder(STAKING_CA, signature)
                           .add_topic(abi_encode_uint(val_id))
                           .add_data(abi_encode_uint(flags))
                           .build();
    emit_log(event);
}

void StakingContract::emit_delegation_event(
    u64_be const val_id, Address const &delegator, u256_be const &amount,
    u64_be const active_epoch)

{
    constexpr bytes32_t signature =
        abi_encode_event_signature("Delegate(uint64,address,uint256,uint64)");
    static_assert(
        signature ==
        0xe4d4df1e1827dd28252fd5c3cd7ebccd3da6e0aa31f74c828f3c8542af49d840_bytes32);

    auto const event = EventBuilder(STAKING_CA, signature)
                           .add_topic(abi_encode_uint(val_id))
                           .add_topic(abi_encode_address(delegator))
                           .add_data(abi_encode_uint(amount))
                           .add_data(abi_encode_uint(active_epoch))
                           .build();
    emit_log(event);
}

void StakingContract::emit_undelegate_event(
    u64_be const val_id, Address const &delegator, u8_be const withdrawal_id,
    u256_be const &amount, u64_be const activation_epoch)
{
    constexpr bytes32_t signature = abi_encode_event_signature(
        "Undelegate(uint64,address,uint8,uint256,uint64)");
    static_assert(
        signature ==
        0x3e53c8b91747e1b72a44894db10f2a45fa632b161fdcdd3a17bd6be5482bac62_bytes32);

    auto const event = EventBuilder(STAKING_CA, signature)
                           .add_topic(abi_encode_uint(val_id))
                           .add_topic(abi_encode_address(delegator))
                           .add_data(abi_encode_uint(withdrawal_id))
                           .add_data(abi_encode_uint(amount))
                           .add_data(abi_encode_uint(activation_epoch))
                           .build();
    emit_log(event);
}

void StakingContract::emit_withdraw_event(
    u64_be const val_id, Address const &delegator, u8_be const withdrawal_id,
    u256_be const &amount)
{
    constexpr bytes32_t signature = abi_encode_event_signature(
        "Withdraw(uint64,address,uint8,uint256,uint64)");
    static_assert(
        signature ==
        0x63030e4238e1146c63f38f4ac81b2b23c8be28882e68b03f0887e50d0e9bb18f_bytes32);

    u64_be const withdraw_epoch = vars.epoch.load();
    auto const event = EventBuilder(STAKING_CA, signature)
                           .add_topic(abi_encode_uint(val_id))
                           .add_topic(abi_encode_address(delegator))
                           .add_data(abi_encode_uint(withdrawal_id))
                           .add_data(abi_encode_uint(amount))
                           .add_data(abi_encode_uint(withdraw_epoch))
                           .build();
    emit_log(event);
}

void StakingContract::emit_claim_rewards_event(
    u64_be const val_id, Address const &delegator, u256_be const &amount)
{
    constexpr bytes32_t signature = abi_encode_event_signature(
        "ClaimRewards(uint64,address,uint256,uint64)");
    static_assert(
        signature ==
        0xcb607e6b63c89c95f6ae24ece9fe0e38a7971aa5ed956254f1df47490921727b_bytes32);

    auto const event = EventBuilder(STAKING_CA, signature)
                           .add_topic(abi_encode_uint(val_id))
                           .add_topic(abi_encode_address(delegator))
                           .add_data(abi_encode_uint(amount))
                           .add_data(abi_encode_uint(vars.epoch.load()))
                           .build();
    emit_log(event);
}

void StakingContract::emit_commission_changed_event(
    u64_be const val_id, u256_be const &old_commission,
    u256_be const &new_commission)
{
    constexpr bytes32_t signature =
        abi_encode_event_signature("CommissionChanged(uint64,uint256,uint256)");
    static_assert(
        signature ==
        0xd1698d3454c5b5384b70aaae33f1704af7c7e055f0c75503ba3146dc28995920_bytes32);

    auto const event = EventBuilder(STAKING_CA, signature)
                           .add_topic(abi_encode_uint(val_id))
                           .add_data(abi_encode_uint(old_commission))
                           .add_data(abi_encode_uint(new_commission))
                           .build();
    emit_log(event);
}

void StakingContract::emit_epoch_changed_event(
    u64_be const old_epoch, u64_be const new_epoch)
{
    constexpr bytes32_t signature =
        abi_encode_event_signature("EpochChanged(uint64,uint64)");
    static_assert(
        signature ==
        0x4fae4dbe0ed659e8ce6637e3c273cd8e4d3bf029b9379a9e8b3f3f27dbef809b_bytes32);

    auto const event = EventBuilder(STAKING_CA, signature)
                           .add_data(abi_encode_uint(old_epoch))
                           .add_data(abi_encode_uint(new_epoch))
                           .build();
    emit_log(event);
}

//////////////
// Helpers //
//////////////

void StakingContract::mint_tokens(uint256_t const &amount)
{
    state_.add_to_balance(STAKING_CA, amount);
}

void StakingContract::send_tokens(Address const &to, uint256_t const &amount)
{
    state_.add_to_balance(to, amount);
    state_.subtract_from_balance(STAKING_CA, amount);
}

uint64_t StakingContract::get_activation_epoch() const noexcept
{
    auto const epoch = vars.epoch.load().native();
    return vars.in_epoch_delay_period.load_checked().has_value() ? epoch + 2
                                                                 : epoch + 1;
}

bool StakingContract::is_epoch_active(
    uint64_t const active_epoch) const noexcept
{
    auto const current_epoch = vars.epoch.load().native();
    return active_epoch != 0 && active_epoch <= current_epoch;
}

void StakingContract::increment_accumulator_refcount(u64_be const val_id)
{
    auto const epoch = get_activation_epoch();
    auto acc_storage = vars.accumulated_reward_per_token(epoch, val_id);
    auto acc = acc_storage.load();
    acc.refcount = acc.refcount.native() + 1;
    acc.value =
        vars.val_execution(val_id).accumulated_reward_per_token().load();
    acc_storage.store(acc);
}

u256_be StakingContract::decrement_accumulator_refcount(
    u64_be const epoch, u64_be const val_id)
{
    auto acc_storage = vars.accumulated_reward_per_token(epoch, val_id);
    auto acc = acc_storage.load();
    auto const value = acc.value;
    auto const refcount = acc.refcount.native();
    if (MONAD_UNLIKELY(refcount == 0)) {
        LOG_INFO(
            "StakingContract: refcount for epoch {} and val_id {} is 0",
            epoch.native(),
            val_id.native());
        return {};
    }
    auto const new_refcount = refcount - 1;
    if (new_refcount == 0) {
        acc_storage.clear();
    }
    else {
        acc.refcount = new_refcount;
        acc_storage.store(acc);
    }
    return value;
}

bool StakingContract::add_to_valset(u64_be const val_id)
{
    uint256_t set = vars.val_bitset_bucket(val_id).load().native();
    uint256_t const mask = 1_u256 << (val_id.native() & 0xFF);
    bool const inserted = !(set & mask);
    set |= mask;
    vars.val_bitset_bucket(val_id).store(set);
    return inserted;
}

void StakingContract::remove_from_valset(u64_be const val_id)
{
    uint256_t set = vars.val_bitset_bucket(val_id).load().native();
    uint256_t const mask = ~(1_u256 << (val_id.native() & 0xFF));
    set &= mask;
    vars.val_bitset_bucket(val_id).store(set);
}

bool can_promote_delta(Delegator const &del, u64_be const &epoch)
{
    return del.get_delta_epoch().native() == 0 &&
           del.get_next_delta_epoch().native() <= epoch.native() + 1;
}

void promote_delta(Delegator &del)
{
    del.delta_stake().store(del.next_delta_stake().load());
    del.next_delta_stake().clear();

    del.set_delta_epoch(del.get_next_delta_epoch());
    del.set_next_delta_epoch(0);
}

Result<uint256_t>
StakingContract::apply_compound(u64_be const val_id, Delegator &del)
{
    auto const epoch_acc =
        decrement_accumulator_refcount(del.get_delta_epoch(), val_id);
    auto const stake = del.stake().load().native();
    auto const delta_stake = del.delta_stake().load().native();
    auto const acc = del.accumulated_reward_per_token().load().native();

    BOOST_OUTCOME_TRY(
        auto const rewards, calculate_rewards(stake, epoch_acc.native(), acc));
    del.accumulated_reward_per_token().store(epoch_acc);

    BOOST_OUTCOME_TRY(
        auto const compounded_stake, checked_add(stake, delta_stake));
    del.stake().store(compounded_stake);

    promote_delta(del);
    return rewards;
}

Result<void>
StakingContract::reward_invariant(ValExecution &val, uint256_t const &rewards)
{
    bool const is_solvent = val.unclaimed_rewards().load().native() >= rewards;

    // revert tx if claiming greater than unclaimed reward balance.
    if (MONAD_UNLIKELY(!is_solvent)) {
        return StakingError::SolvencyError;
    }
    auto const old_unclaimed = val.unclaimed_rewards().load().native();
    BOOST_OUTCOME_TRY(
        auto const unclaimed_rewards, checked_sub(old_unclaimed, rewards));
    val.unclaimed_rewards().store(unclaimed_rewards);

    return outcome::success();
}

Result<void>
StakingContract::pull_delegator_up_to_date(u64_be const val_id, Delegator &del)
{
    // move up next_delta_epoch
    if (can_promote_delta(del, vars.epoch.load())) {
        promote_delta(del);
    }
    auto val = vars.val_execution(val_id);

    bool const can_compound = is_epoch_active(del.get_delta_epoch().native());
    bool const can_compound_boundary =
        is_epoch_active(del.get_next_delta_epoch().native());
    if (MONAD_UNLIKELY(can_compound_boundary)) {
        MONAD_ASSERT_THROW(
            can_compound,
            "staking compound logic error"); // only set when user compounds
                                             // before and after block boundary
        BOOST_OUTCOME_TRY(auto rewards, apply_compound(val_id, del));
        BOOST_OUTCOME_TRY(reward_invariant(val, rewards));
        BOOST_OUTCOME_TRY(
            u256_be const new_rewards,
            checked_add(del.rewards().load().native(), rewards));
        del.rewards().store(new_rewards);
    }
    if (MONAD_UNLIKELY(can_compound)) {
        BOOST_OUTCOME_TRY(auto rewards, apply_compound(val_id, del));
        BOOST_OUTCOME_TRY(reward_invariant(val, rewards));
        BOOST_OUTCOME_TRY(
            u256_be const new_rewards,
            checked_add(del.rewards().load().native(), rewards));
        del.rewards().store(new_rewards);
    }
    if (del.stake().load().native() == 0) {
        // Running the below code is perfectly fine if delegator stake is zero.
        // However, we set del.acc = val.acc, which is wasteful.
        return outcome::success();
    }

    BOOST_OUTCOME_TRY(
        auto const rewards,
        calculate_rewards(
            del.stake().load().native(),
            val.accumulated_reward_per_token().load().native(),
            del.accumulated_reward_per_token().load().native()));
    BOOST_OUTCOME_TRY(reward_invariant(val, rewards));

    // update delegator state
    BOOST_OUTCOME_TRY(
        u256_be const new_rewards,
        checked_add(del.rewards().load().native(), rewards));
    del.rewards().store(new_rewards);
    del.accumulated_reward_per_token().store(
        val.accumulated_reward_per_token().load());
    return outcome::success();
}

Result<void> StakingContract::apply_reward(
    u64_be const val_id, Address const &from, uint256_t const &new_rewards,
    uint256_t const &active_stake)
{
    // 1. compute current acc value
    BOOST_OUTCOME_TRY(
        auto const reward_acc,
        checked_mul_div(new_rewards, UNIT_BIAS, active_stake));

    // 2. add to accumulator
    auto val_execution = vars.val_execution(val_id);
    BOOST_OUTCOME_TRY(
        auto const acc,
        checked_add(
            val_execution.accumulated_reward_per_token().load().native(),
            reward_acc));
    val_execution.accumulated_reward_per_token().store(acc);

    // 3. compute new unclaimed rewards
    BOOST_OUTCOME_TRY(
        auto const unclaimed_rewards,
        checked_add(
            val_execution.unclaimed_rewards().load().native(), new_rewards));

    // 4. include in unclaimed rewards
    val_execution.unclaimed_rewards().store(unclaimed_rewards);

    emit_validator_rewarded_event(val_id, from, new_rewards);

    return outcome::success();
}

///////////////////
//  Precompiles  //
///////////////////

std::pair<StakingContract::PrecompileFunc, uint64_t>
StakingContract::precompile_dispatch(byte_string_view &input)
{
    if (MONAD_UNLIKELY(input.size() < 4)) {
        return make_pair(&StakingContract::precompile_fallback, 40000);
    }

    auto const signature =
        intx::be::unsafe::load<uint32_t>(input.substr(0, 4).data());
    input.remove_prefix(4);

    switch (signature) {
    case PrecompileSelector::ADD_VALIDATOR:
        // [21, 22, 6, 15, 9, 3, 0]
        return {
            &StakingContract::precompile_add_validator, ADD_VALIDATOR_OP_COST};
    case PrecompileSelector::DELEGATE:
        // [21, 17, 6, 14, 5, 2, 0]
        return {&StakingContract::precompile_delegate, DELEGATE_OP_COST};
    case PrecompileSelector::UNDELEGATE:
        // [15, 11, 8, 5, 1, 2, 0]
        return {&StakingContract::precompile_undelegate, UNDELEGATE_OP_COST};
    case PrecompileSelector::COMPOUND:
        // [46, 17, 6, 29, 3, 2, 0]
        return {&StakingContract::precompile_compound, COMPOUND_OP_COST};
    case PrecompileSelector::WITHDRAW:
        // [11, 6, 1, 0, 0, 1, 1]
        return {&StakingContract::precompile_withdraw, WITHDRAW_OP_COST};
    case PrecompileSelector::CLAIM_REWARDS:
        // [16, 11, 2, 11, 1, 1, 1]
        return {
            &StakingContract::precompile_claim_rewards, CLAIM_REWARDS_OP_COST};
    case PrecompileSelector::CHANGE_COMMISSION:
        // [0, 3, 0, 0, 1, 1, 0]
        return {
            &StakingContract::precompile_change_commission,
            CHANGE_COMMISSION_OP_COST};
    case PrecompileSelector::EXTERNAL_REWARD:
        // [0, 5, 0, 0, 2, 0, 0]
        return {
            &StakingContract::precompile_external_reward,
            EXTERNAL_REWARDS_OP_COST};
    case PrecompileSelector::GET_EPOCH:
        // [0, 2, 0, 0, 0, 0, 0]
        return {&StakingContract::precompile_get_epoch, GET_EPOCH_OP_COST};
    case PrecompileSelector::GET_VALIDATOR:
        // [0, 12, 0, 0, 0, 0, 0]
        return {
            &StakingContract::precompile_get_validator, GET_VALIDATOR_OP_COST};
    case PrecompileSelector::GET_DELEGATOR:
        // [15, 17, 1, 11, 1, 0, 0]
        return {
            &StakingContract::precompile_get_delegator, GET_DELEGATOR_OP_COST};
    case PrecompileSelector::GET_WITHDRAWAL_REQUEST:
        // [0, 3, 0, 0, 0, 0, 0]
        return {
            &StakingContract::precompile_get_withdrawal_request,
            GET_WITHDRAWAL_REQUEST_OP_COST};
    case PrecompileSelector::GET_CONSENSUS_VALIDATOR_SET:
        // [0,100,0,0,0,0,0]
        return {
            &StakingContract::precompile_get_consensus_valset,
            GET_VALIDATOR_SET_OP_COST};
    case PrecompileSelector::GET_SNAPSHOT_VALIDATOR_SET:
        // [0,100,0,0,0,0,0]
        return {
            &StakingContract::precompile_get_snapshot_valset,
            GET_VALIDATOR_SET_OP_COST};
    case PrecompileSelector::GET_EXECUTION_VALIDATOR_SET:
        // [0,100,0,0,0,0,0]
        return {
            &StakingContract::precompile_get_execution_valset,
            GET_VALIDATOR_SET_OP_COST};
    case PrecompileSelector::GET_DELEGATIONS:
        // [0,100,0,0,0,0,0]
        return {
            &StakingContract::precompile_get_delegations,
            LINKED_LIST_GETTER_OP_COST};
    case PrecompileSelector::GET_DELEGATORS:
        // [0,100,0,0,0,0,0]
        return {
            &StakingContract::precompile_get_delegators,
            LINKED_LIST_GETTER_OP_COST};
    default:
        return {&StakingContract::precompile_fallback, 40000};
    }
}

std::tuple<bool, u32_be, std::vector<u64_be>> StakingContract::get_valset(
    StorageArray<u64_be> const &valset, uint32_t const start_index,
    uint32_t const limit)
{
    uint64_t const len = valset.length();
    uint64_t const end =
        std::min(len, static_cast<uint64_t>(start_index) + limit);
    std::vector<u64_be> valids;
    uint64_t i;
    for (i = start_index; i < end; ++i) {
        valids.push_back(valset.get(i).load());
    }
    bool const done = (end == len);
    return {done, static_cast<uint32_t>(i), std::move(valids)};
}

std::tuple<bool, Address, std::vector<Address>>
StakingContract::get_delegators_for_validator(
    u64_be val_id, Address const &start_delegator, uint32_t const limit)
{
    return linked_list_traverse<u64_be, Address>(
        val_id, start_delegator, limit);
}

std::tuple<bool, u64_be, std::vector<u64_be>>
StakingContract::get_validators_for_delegator(
    Address const &delegator, u64_be const start_val_id, uint32_t const limit)
{
    return linked_list_traverse<Address, u64_be>(
        delegator, start_val_id, limit);
}

Result<byte_string> StakingContract::precompile_get_validator(
    byte_string_view input, evmc_address const &,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    BOOST_OUTCOME_TRY(auto const val_id, abi_decode_fixed<u64_be>(input));
    if (MONAD_UNLIKELY(!input.empty())) {
        return StakingError::InvalidInput;
    }

    auto val = vars.val_execution(val_id);
    auto consensus_view = vars.consensus_view(val_id);
    auto snapshot_view = vars.snapshot_view(val_id);

    AbiEncoder encoder;
    auto const af = val.address_flags().load();
    encoder.add_address(af.auth_address);
    encoder.add_uint(af.flags);
    encoder.add_uint(val.stake().load());
    encoder.add_uint(val.accumulated_reward_per_token().load());
    encoder.add_uint(val.commission().load());
    encoder.add_uint(val.unclaimed_rewards().load());
    encoder.add_uint(consensus_view.stake().load());
    encoder.add_uint(consensus_view.commission().load());
    encoder.add_uint(snapshot_view.stake().load());
    encoder.add_uint(snapshot_view.commission().load());

    auto const k = val.keys().load();
    encoder.add_bytes(to_byte_string_view(k.secp_pubkey));
    encoder.add_bytes(to_byte_string_view(k.bls_pubkey));

    return encoder.encode_final();
}

Result<byte_string> StakingContract::precompile_get_delegator(
    byte_string_view input, evmc_address const &,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    BOOST_OUTCOME_TRY(auto const val_id, abi_decode_fixed<u64_be>(input));
    BOOST_OUTCOME_TRY(auto const address, abi_decode_fixed<Address>(input));
    if (MONAD_UNLIKELY(!input.empty())) {
        return StakingError::InvalidInput;
    }

    auto del = vars.delegator(val_id, address);
    BOOST_OUTCOME_TRY(pull_delegator_up_to_date(val_id, del));

    AbiEncoder encoder;
    encoder.add_uint(del.stake().load());
    encoder.add_uint(del.accumulated_reward_per_token().load());
    encoder.add_uint(del.rewards().load());
    encoder.add_uint(del.delta_stake().load());
    encoder.add_uint(del.next_delta_stake().load());

    auto const e = del.epochs().load();
    encoder.add_uint(e.delta_epoch);
    encoder.add_uint(e.next_delta_epoch);

    return encoder.encode_final();
}

Result<byte_string> StakingContract::get_valset(
    byte_string_view input, StorageArray<u64_be> const &valset)
{
    BOOST_OUTCOME_TRY(auto const start_index, abi_decode_fixed<u32_be>(input));
    if (MONAD_UNLIKELY(!input.empty())) {
        return StakingError::InvalidInput;
    }

    if (MONAD_UNLIKELY(
            valset.length() > std::numeric_limits<uint32_t>::max())) {
        // Both consensus set and snapshot set are bounded. The execution set is
        // theoretically unbounded, but to be a candidate, you need to put
        // MIN_VALIDATE_STAKE. This amount prevents that valset from exceeding
        // u32_max in practice.
        return StakingError::InternalError;
    }

    auto const [done, next_index, valids] =
        get_valset(valset, start_index.native(), PAGINATED_RESULTS_SIZE);
    AbiEncoder encoder;
    encoder.add_bool(done);
    encoder.add_uint(next_index);
    encoder.add_uint_array(valids);
    return encoder.encode_final();
}

Result<byte_string> StakingContract::precompile_get_consensus_valset(
    byte_string_view const input, evmc_address const &,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));
    return get_valset(input, vars.valset_consensus);
}

Result<byte_string> StakingContract::precompile_get_snapshot_valset(
    byte_string_view const input, evmc_address const &,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));
    return get_valset(input, vars.valset_snapshot);
}

Result<byte_string> StakingContract::precompile_get_execution_valset(
    byte_string_view const input, evmc_address const &,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));
    auto const valset = vars.valset_execution;
    return get_valset(input, valset);
}

Result<byte_string> StakingContract::precompile_get_delegations(
    byte_string_view input, evmc_address const &,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    BOOST_OUTCOME_TRY(auto const delegator, abi_decode_fixed<Address>(input));
    BOOST_OUTCOME_TRY(auto const start_val_id, abi_decode_fixed<u64_be>(input));
    if (MONAD_UNLIKELY(!input.empty())) {
        return StakingError::InvalidInput;
    }

    auto const [done, next_val_id, vals_page] = get_validators_for_delegator(
        delegator, start_val_id, PAGINATED_RESULTS_SIZE);

    AbiEncoder encoder;
    encoder.add_bool(done);
    encoder.add_uint(next_val_id);
    encoder.add_uint_array(vals_page);
    return encoder.encode_final();
}

Result<byte_string> StakingContract::precompile_get_delegators(
    byte_string_view input, evmc_address const &,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    BOOST_OUTCOME_TRY(auto const val_id, abi_decode_fixed<u64_be>(input));
    BOOST_OUTCOME_TRY(
        auto const start_delegator_address, abi_decode_fixed<Address>(input));
    if (MONAD_UNLIKELY(!input.empty())) {
        return StakingError::InvalidInput;
    }

    auto const [done, next_del_addr, dels_page] = get_delegators_for_validator(
        val_id, start_delegator_address, PAGINATED_RESULTS_SIZE);

    AbiEncoder encoder;
    encoder.add_bool(done);
    encoder.add_address(next_del_addr);
    encoder.add_address_array(dels_page);
    return encoder.encode_final();
}

Result<byte_string> StakingContract::precompile_get_epoch(
    byte_string_view const, evmc_address const &,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    AbiEncoder encoder;
    encoder.add_uint(vars.epoch.load());
    encoder.add_bool(vars.in_epoch_delay_period.load());
    return encoder.encode_final();
}

Result<byte_string> StakingContract::precompile_get_withdrawal_request(
    byte_string_view input, evmc_address const &,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    BOOST_OUTCOME_TRY(auto const val_id, abi_decode_fixed<u64_be>(input));
    BOOST_OUTCOME_TRY(auto const delegator, abi_decode_fixed<Address>(input));
    BOOST_OUTCOME_TRY(auto const withdrawal_id, abi_decode_fixed<u8_be>(input));
    if (MONAD_UNLIKELY(!input.empty())) {
        return StakingError::InvalidInput;
    }

    auto const request =
        vars.withdrawal_request(val_id, delegator, withdrawal_id).load();

    AbiEncoder encoder;
    encoder.add_uint(request.amount);
    encoder.add_uint(request.acc);
    encoder.add_uint(request.epoch);
    return encoder.encode_final();
}

Result<byte_string> StakingContract::precompile_fallback(
    byte_string_view const, evmc_address const &, evmc_uint256be const &)
{
    return StakingError::MethodNotSupported;
}

// TODO: Track solvency
Result<byte_string> StakingContract::precompile_add_validator(
    byte_string_view input, evmc_address const &,
    evmc_uint256be const &msg_value)
{
    constexpr size_t MESSAGE_SIZE = 33 /* compressed secp pubkey */ +
                                    48 /* compressed bls pubkey */ +
                                    sizeof(Address) /* auth address */ +
                                    sizeof(u256_be) /* signed stake */ +
                                    sizeof(u256_be) /* commission rate */;
    // decode the head
    BOOST_OUTCOME_TRY(
        abi_decode_fixed<u256_be>(input)); // skip message tail offset
    BOOST_OUTCOME_TRY(
        abi_decode_fixed<u256_be>(input)); // skip secp sig tail offset
    BOOST_OUTCOME_TRY(
        abi_decode_fixed<u256_be>(input)); // sip bls sig tail offset

    // decode bytes with known lengths from the tail
    BOOST_OUTCOME_TRY(
        auto const message, abi_decode_bytes_tail<MESSAGE_SIZE>(input));
    BOOST_OUTCOME_TRY(
        auto const secp_signature_compressed, abi_decode_bytes_tail<64>(input));
    BOOST_OUTCOME_TRY(
        auto const bls_signature_compressed, abi_decode_bytes_tail<96>(input));

    if (MONAD_UNLIKELY(!input.empty())) {
        return StakingError::InvalidInput;
    }

    // extract individual inputs from the message
    byte_string_view reader = to_byte_string_view(message);
    auto const secp_pubkey_compressed =
        unaligned_load<byte_string_fixed<33>>(consume_bytes(reader, 33).data());
    auto const bls_pubkey_compressed =
        unaligned_load<byte_string_fixed<48>>(consume_bytes(reader, 48).data());
    auto const auth_address =
        unaligned_load<Address>(consume_bytes(reader, sizeof(Address)).data());
    auto const signed_stake = unaligned_load<evmc_uint256be>(
        consume_bytes(reader, sizeof(evmc_uint256be)).data());
    auto const commission =
        unaligned_load<u256_be>(consume_bytes(reader, sizeof(u256_be)).data());

    if (MONAD_UNLIKELY(
            0 !=
            memcmp(
                signed_stake.bytes, msg_value.bytes, sizeof(evmc_uint256be)))) {
        return StakingError::InvalidInput;
    }

    auto const stake = intx::be::load<uint256_t>(msg_value);
    if (MONAD_UNLIKELY(stake < MIN_VALIDATE_STAKE)) {
        return StakingError::InsufficientStake;
    }

    // Verify SECP signature
    Secp256k1Pubkey secp_pubkey(secp_pubkey_compressed);
    if (MONAD_UNLIKELY(!secp_pubkey.is_valid())) {
        return StakingError::InvalidSecpPubkey;
    }
    Secp256k1Signature secp_sig(secp_signature_compressed);
    if (MONAD_UNLIKELY(!secp_sig.is_valid())) {
        return StakingError::InvalidSecpSignature;
    }
    if (MONAD_UNLIKELY(
            !secp_sig.verify(secp_pubkey, to_byte_string_view(message)))) {
        return StakingError::SecpSignatureVerificationFailed;
    }

    // Verify BLS signature
    BlsPubkey bls_pubkey(bls_pubkey_compressed);
    if (MONAD_UNLIKELY(!bls_pubkey.is_valid())) {
        return StakingError::InvalidBlsPubkey;
    }
    BlsSignature bls_sig(bls_signature_compressed);
    if (MONAD_UNLIKELY(!bls_sig.is_valid())) {
        return StakingError::InvalidBlsSignature;
    }
    if (MONAD_UNLIKELY(
            !bls_sig.verify(bls_pubkey, to_byte_string_view(message)))) {
        return StakingError::BlsSignatureVerificationFailed;
    }

    if (MONAD_UNLIKELY(commission.native() > MAX_COMMISSION)) {
        return StakingError::CommissionTooHigh;
    }

    // Check if validator already exists
    auto const secp_eth_address = address_from_secpkey(secp_pubkey.serialize());
    auto const bls_eth_address = address_from_bls_key(bls_pubkey.serialize());
    auto val_id_storage = vars.val_id(secp_eth_address);
    auto val_id_bls_storage = vars.val_id_bls(bls_eth_address);
    if (MONAD_UNLIKELY(
            val_id_storage.load_checked().has_value() ||
            val_id_bls_storage.load_checked().has_value())) {
        return StakingError::ValidatorExists;
    }

    u64_be const val_id = vars.last_val_id.load().native() + 1;
    val_id_storage.store(val_id);
    val_id_bls_storage.store(val_id);
    vars.last_val_id.store(val_id);

    // add validator metadata
    auto val = vars.val_execution(val_id);
    val.keys().store(KeysPacked{
        .secp_pubkey = secp_pubkey_compressed,
        .bls_pubkey = bls_pubkey_compressed});
    val.address_flags().store(AddressFlags{
        .auth_address = auth_address, .flags = ValidatorFlagsStakeTooLow});
    val.commission().store(commission);

    emit_validator_created_event(val_id, auth_address, commission);

    BOOST_OUTCOME_TRY(delegate(val_id, stake, auth_address));
    return byte_string{abi_encode_uint(val_id)};
}

Result<void> StakingContract::delegate(
    u64_be const val_id, uint256_t const &stake, Address const &address)
{
    auto val = vars.val_execution(val_id);
    if (MONAD_UNLIKELY(!val.exists())) {
        return StakingError::UnknownValidator;
    }

    if (MONAD_UNLIKELY(stake < DUST_THRESHOLD)) {
        // Each individual delegation must be greater than a dust threshold.
        // While it may seem more intuitive to fail only if the delegator's
        // total stake less than the dust threshold. But a delegator could, for
        // instance, compound dust then undelegate their active stake
        // afterwards.  In the following epoch, the remaining active stake would
        // be dust.  Therefore, a stricter gate threshold applied to each
        // delegation is easier to reason about. It's also unlikely anyone would
        // want to pay to delegate sub-MON amounts.
        return StakingError::DelegationTooSmall;
    }

    auto del = vars.delegator(val_id, address);
    BOOST_OUTCOME_TRY(pull_delegator_up_to_date(val_id, del));

    bool need_future_accumulator = false;
    u64_be const active_epoch = get_activation_epoch();

    // re-delegation: check if stake needs to be compounded, and when.
    if (vars.in_epoch_delay_period.load()) {
        // case 1: compound called in boundary. becomes active in epoch+2
        need_future_accumulator = (del.get_next_delta_epoch().native() == 0);
        BOOST_OUTCOME_TRY(
            auto const delta,
            checked_add(del.next_delta_stake().load().native(), stake));
        del.next_delta_stake().store(delta);
        del.set_next_delta_epoch(active_epoch);
    }
    else {
        // case 2: compound called before boundary. becomes active in
        // epoch+1
        need_future_accumulator = (del.get_delta_epoch().native() == 0);
        BOOST_OUTCOME_TRY(
            auto const delta,
            checked_add(del.delta_stake().load().native(), stake));
        del.delta_stake().store(delta);
        del.set_delta_epoch(active_epoch);
    }

    if (need_future_accumulator) {
        increment_accumulator_refcount(val_id);
    }
    emit_delegation_event(val_id, address, stake, active_epoch);

    BOOST_OUTCOME_TRY(
        auto const new_val_stake,
        checked_add(val.stake().load().native(), stake));
    val.stake().store(new_val_stake);

    // does total val stake exceed the minimum threshold?
    auto const oldflags = val.get_flags();
    if (new_val_stake >= ACTIVE_VALIDATOR_STAKE) {
        val.clear_flag(ValidatorFlagsStakeTooLow);
    }
    // did the auth delegator reactivate?
    if (val.auth_address() == address &&
        del.get_next_epoch_stake() >= MIN_VALIDATE_STAKE) {
        val.clear_flag(ValidatorFlagWithdrawn);
    }
    if (val.get_flags() != oldflags) {
        emit_validator_status_changed_event(val_id, val.get_flags());
    }

    if (val.get_flags() == ValidatorFlagsOk) {
        bool const inserted = add_to_valset(val_id);
        if (inserted) {
            vars.valset_execution.push(val_id);
        }
    }

    BOOST_OUTCOME_TRY(
        linked_list_insert(val_id, address)); // validator => List[Delegator]
    BOOST_OUTCOME_TRY(
        linked_list_insert(address, val_id)); // delegator => List[Validator]

    return outcome::success();
}

Result<byte_string> StakingContract::precompile_delegate(
    byte_string_view input, evmc_address const &msg_sender,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(auto const val_id, abi_decode_fixed<u64_be>(input));
    if (MONAD_UNLIKELY(!input.empty())) {
        return StakingError::InvalidInput;
    }
    auto const stake = intx::be::load<uint256_t>(msg_value);

    if (MONAD_LIKELY(stake != 0)) {
        BOOST_OUTCOME_TRY(delegate(val_id, stake, msg_sender));
    }
    return byte_string{abi_encode_bool(true)};
}

Result<byte_string> StakingContract::precompile_undelegate(
    byte_string_view input, evmc_address const &msg_sender,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    BOOST_OUTCOME_TRY(auto const val_id, abi_decode_fixed<u64_be>(input));
    BOOST_OUTCOME_TRY(auto const stake, abi_decode_fixed<u256_be>(input));
    BOOST_OUTCOME_TRY(auto const withdrawal_id, abi_decode_fixed<u8_be>(input));
    if (MONAD_UNLIKELY(!input.empty())) {
        return StakingError::InvalidInput;
    }

    auto amount = stake.native();

    if (MONAD_UNLIKELY(amount == 0)) {
        return byte_string{abi_encode_bool(true)};
    }

    auto val = vars.val_execution(val_id);
    if (MONAD_UNLIKELY(!val.exists())) {
        return StakingError::UnknownValidator;
    }

    auto withdrawal_request =
        vars.withdrawal_request(val_id, msg_sender, withdrawal_id)
            .load_checked();
    if (MONAD_UNLIKELY(withdrawal_request.has_value())) {
        return StakingError::WithdrawalIdExists;
    }

    auto del = vars.delegator(val_id, msg_sender);
    BOOST_OUTCOME_TRY(pull_delegator_up_to_date(val_id, del));
    uint256_t val_stake = val.stake().load().native();
    uint256_t del_stake = del.stake().load().native();

    if (MONAD_UNLIKELY(del_stake < amount)) {
        return StakingError::InsufficientStake;
    }

    BOOST_OUTCOME_TRY(val_stake, checked_sub(val_stake, amount));
    BOOST_OUTCOME_TRY(del_stake, checked_sub(del_stake, amount));
    if (MONAD_UNLIKELY(del_stake < DUST_THRESHOLD)) {
        // if all that remains is dust, send the rest of the delegator's balance
        // with this withdrawal.
        BOOST_OUTCOME_TRY(amount, checked_add(amount, del_stake));
        BOOST_OUTCOME_TRY(val_stake, checked_sub(val_stake, del_stake));
        del_stake = 0;
    }
    val.stake().store(val_stake);
    del.stake().store(del_stake);
    u64_be const withdrawal_epoch = get_activation_epoch();

    auto const oldflags = val.get_flags();
    if (msg_sender == val.auth_address() &&
        del.get_next_epoch_stake() < MIN_VALIDATE_STAKE) {
        val.set_flag(ValidatorFlagWithdrawn);
    }
    if (val_stake < ACTIVE_VALIDATOR_STAKE) {
        val.set_flag(ValidatorFlagsStakeTooLow);
    }
    if (val.get_flags() != oldflags) {
        emit_validator_status_changed_event(val_id, val.get_flags());
    }
    emit_undelegate_event(
        val_id, msg_sender, withdrawal_id, amount, withdrawal_epoch);

    // each withdrawal request can be thought of as an independent delegator
    // whose stake is the amount being withdrawn.
    vars.withdrawal_request(val_id, msg_sender, withdrawal_id)
        .store(WithdrawalRequest{
            .amount = amount,
            .acc = del.accumulated_reward_per_token().load(),
            .epoch = withdrawal_epoch});
    increment_accumulator_refcount(val_id);

    if (del.stake().load().native() == 0) {
        // consensus view of stake is zero. should this user re-delegate, he
        // will receive a new accumulator. this frees up state.
        del.accumulated_reward_per_token().clear();
    }

    if (del.get_next_epoch_stake() == 0) {
        linked_list_remove(val_id, static_cast<Address>(msg_sender));
        linked_list_remove(static_cast<Address>(msg_sender), val_id);
    }

    return byte_string{abi_encode_bool(true)};
}

// TODO: No compounds allowed if auth_address is under sufficent amount.
Result<byte_string> StakingContract::precompile_compound(
    byte_string_view input, evmc_address const &msg_sender,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    BOOST_OUTCOME_TRY(auto const val_id, abi_decode_fixed<u64_be>(input));
    if (MONAD_UNLIKELY(!input.empty())) {
        return StakingError::InvalidInput;
    }

    auto del = vars.delegator(val_id, msg_sender);
    BOOST_OUTCOME_TRY(pull_delegator_up_to_date(val_id, del));
    auto rewards_slot = del.rewards();
    uint256_t const rewards = rewards_slot.load().native();
    rewards_slot.clear();

    if (MONAD_UNLIKELY(rewards != 0)) {
        // A compound call is essentially a helper for a `claimRewards()` call
        // followed by a `delegate()` call. For offchain programs to track the
        // flow of rewards leaving delegation using events only, this aids in
        // double-counting errors.
        emit_claim_rewards_event(val_id, msg_sender, rewards);
        BOOST_OUTCOME_TRY(delegate(val_id, rewards, msg_sender));
    }

    return byte_string{abi_encode_bool(true)};
}

Result<byte_string> StakingContract::precompile_withdraw(
    byte_string_view input, evmc_address const &msg_sender,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    BOOST_OUTCOME_TRY(auto const val_id, abi_decode_fixed<u64_be>(input));
    BOOST_OUTCOME_TRY(auto const withdrawal_id, abi_decode_fixed<u8_be>(input));
    if (MONAD_UNLIKELY(!input.empty())) {
        return StakingError::InvalidInput;
    }

    auto withdrawal_request_storage =
        vars.withdrawal_request(val_id, msg_sender, withdrawal_id);
    auto withdrawal_request = withdrawal_request_storage.load_checked();
    if (MONAD_UNLIKELY(!withdrawal_request.has_value())) {
        return StakingError::UnknownWithdrawalId;
    }
    withdrawal_request_storage.clear();

    bool const ready =
        is_epoch_active(withdrawal_request->epoch.native() + WITHDRAWAL_DELAY);
    if (MONAD_UNLIKELY(!ready)) {
        return StakingError::WithdrawalNotReady;
    }

    auto withdraw_acc =
        decrement_accumulator_refcount(withdrawal_request->epoch, val_id)
            .native();
    auto withdrawal_amount = withdrawal_request->amount.native();
    BOOST_OUTCOME_TRY(
        auto const rewards,
        calculate_rewards(
            withdrawal_amount, withdraw_acc, withdrawal_request->acc.native()));
    auto val = vars.val_execution(val_id);
    BOOST_OUTCOME_TRY(reward_invariant(val, rewards));

    BOOST_OUTCOME_TRY(
        withdrawal_amount, checked_add(withdrawal_amount, rewards));
    auto const contract_balance =
        intx::be::load<uint256_t>(state_.get_balance(STAKING_CA));
    MONAD_ASSERT_THROW(
        contract_balance >= withdrawal_amount, "withdrawal insolvent");
    send_tokens(msg_sender, withdrawal_amount);

    emit_withdraw_event(val_id, msg_sender, withdrawal_id, withdrawal_amount);

    return byte_string{abi_encode_bool(true)};
}

Result<byte_string> StakingContract::precompile_claim_rewards(
    byte_string_view input, evmc_address const &msg_sender,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    BOOST_OUTCOME_TRY(auto const val_id, abi_decode_fixed<u64_be>(input));
    if (MONAD_UNLIKELY(!input.empty())) {
        return StakingError::InvalidInput;
    }
    auto del = vars.delegator(val_id, msg_sender);
    BOOST_OUTCOME_TRY(pull_delegator_up_to_date(val_id, del));

    auto const rewards = del.rewards().load();
    if (MONAD_LIKELY(rewards.native() != 0)) {
        send_tokens(msg_sender, rewards.native());
        del.rewards().clear();
        emit_claim_rewards_event(val_id, msg_sender, rewards);
    }

    return byte_string{abi_encode_bool(true)};
}

Result<byte_string> StakingContract::precompile_change_commission(
    byte_string_view input, evmc_address const &msg_sender,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    BOOST_OUTCOME_TRY(auto const val_id, abi_decode_fixed<u64_be>(input));
    BOOST_OUTCOME_TRY(
        auto const new_commission, abi_decode_fixed<u256_be>(input));
    if (MONAD_UNLIKELY(!input.empty())) {
        return StakingError::InvalidInput;
    }

    auto validator = vars.val_execution(val_id);
    if (MONAD_UNLIKELY(!validator.exists())) {
        return StakingError::UnknownValidator;
    }

    if (MONAD_UNLIKELY(msg_sender != validator.auth_address())) {
        return StakingError::RequiresAuthAddress;
    }

    if (MONAD_UNLIKELY(new_commission.native() > MAX_COMMISSION)) {
        return StakingError::CommissionTooHigh;
    }

    // set in execution view. will go live next epoch.
    u256_be const old_commission = validator.commission().load();
    if (MONAD_LIKELY(old_commission != new_commission)) {
        validator.commission().store(new_commission);
        emit_commission_changed_event(val_id, old_commission, new_commission);
    }

    return byte_string{abi_encode_bool(true)};
}

Result<byte_string> StakingContract::precompile_external_reward(
    byte_string_view input, evmc_address const &sender,
    evmc_uint256be const &msg_value)
{
    auto const external_reward = intx::be::load<uint256_t>(msg_value);
    BOOST_OUTCOME_TRY(auto const val_id, abi_decode_fixed<u64_be>(input));
    if (MONAD_UNLIKELY(!input.empty())) {
        return StakingError::InvalidInput;
    }

    // 1. Only validators in the consensus set can invoke this method.
    auto val_execution = vars.val_execution(val_id);
    if (MONAD_UNLIKELY(!val_execution.exists())) {
        return StakingError::UnknownValidator;
    }
    auto consensus_view = vars.this_epoch_view(val_id);
    uint256_t const active_stake = consensus_view.stake().load().native();
    if (MONAD_UNLIKELY(active_stake == 0)) {
        return StakingError::NotInValidatorSet;
    }

    // 2. Apply bounds checks
    if (MONAD_UNLIKELY(external_reward < MIN_EXTERNAL_REWARD)) {
        return StakingError::ExternalRewardTooSmall;
    }
    if (MONAD_UNLIKELY(external_reward > MAX_EXTERNAL_REWARD)) {
        return StakingError::ExternalRewardTooLarge;
    }

    // 3. Update validator accumulator.
    BOOST_OUTCOME_TRY(
        apply_reward(val_id, sender, external_reward, active_stake));

    return byte_string{abi_encode_bool(true)};
}

////////////////////
//  System Calls  //
////////////////////

Result<void> StakingContract::syscall_on_epoch_change(byte_string_view input)
{
    BOOST_OUTCOME_TRY(u64_be const next_epoch, abi_decode_fixed<u64_be>(input));
    if (MONAD_UNLIKELY(!input.empty())) {
        return StakingError::InvalidInput;
    }

    u64_be const next_next_epoch = next_epoch.native() + 1;
    u64_be const last_epoch = vars.epoch.load();
    if (MONAD_UNLIKELY(next_epoch.native() <= last_epoch.native())) {
        LOG_ERROR(
            "Invalid epoch change: from {} to {}",
            last_epoch.native(),
            next_epoch.native());
        return StakingError::InvalidEpochChange;
    }

    emit_epoch_changed_event(last_epoch, next_epoch);

    auto const valset = vars.valset_snapshot;
    uint64_t const num_active_vals = valset.length();
    for (uint64_t i = 0; i < num_active_vals; ++i) {
        auto const val_id = valset.get(i).load();
        auto val = vars.val_execution(val_id);

        // TODO: once Maged's speculative execution is merged, move this
        // into a separate loop.
        {
            auto acc_storage =
                vars.accumulated_reward_per_token(next_epoch, val_id);
            auto acc = acc_storage.load_checked();
            if (acc.has_value()) {
                acc->value = val.accumulated_reward_per_token().load();
                acc_storage.store(*acc);
            }
        }
        {
            auto acc_storage =
                vars.accumulated_reward_per_token(next_next_epoch, val_id);
            auto acc = acc_storage.load_checked();
            if (acc.has_value()) {
                acc->value = val.accumulated_reward_per_token().load();
                acc_storage.store(*acc);
            }
        }
    }

    vars.in_epoch_delay_period.clear();
    vars.epoch.store(next_epoch);

    return outcome::success();
}

// update rewards for leader only if in active validator set
Result<void> StakingContract::syscall_reward(
    byte_string_view input, uint256_t const &raw_reward)
{
    BOOST_OUTCOME_TRY(
        auto const block_author, abi_decode_fixed<Address>(input));
    if (MONAD_UNLIKELY(!input.empty())) {
        return StakingError::InvalidInput;
    }

    // 1. get validator information
    auto const val_id = vars.val_id(block_author).load_checked();
    if (MONAD_UNLIKELY(!val_id.has_value())) {
        return StakingError::NotInValidatorSet;
    }

    // 2. validator must be active
    auto consensus_view = vars.this_epoch_view(val_id.value());
    uint256_t const active_stake = consensus_view.stake().load().native();
    if (MONAD_UNLIKELY(active_stake == 0)) {
        // Validator cannot be in the active set with no stake
        return StakingError::NotInValidatorSet;
    }

    mint_tokens(raw_reward);

    // 3. subtract commission
    uint256_t const commission_rate =
        consensus_view.commission().load().native();
    BOOST_OUTCOME_TRY(
        auto const commission,
        checked_mul_div(raw_reward, commission_rate, MON));

    // 4. Send commission to the auth address
    auto val_execution = vars.val_execution(val_id.value());
    auto auth = vars.delegator(val_id.value(), val_execution.auth_address());
    BOOST_OUTCOME_TRY(
        auto const auth_reward,
        checked_add(auth.rewards().load().native(), commission));
    auth.rewards().store(auth_reward);

    BOOST_OUTCOME_TRY(
        auto const del_reward, checked_sub(raw_reward, commission));
    // 5. update accumulator and unclaimed rewards for this validator pool
    BOOST_OUTCOME_TRY(
        apply_reward(val_id.value(), SYSTEM_SENDER, del_reward, active_stake));

    return outcome::success();
}

Result<void> StakingContract::syscall_snapshot(byte_string_view const input)
{
    if (MONAD_UNLIKELY(!input.empty())) {
        return StakingError::InvalidInput;
    }
    if (MONAD_UNLIKELY(vars.in_epoch_delay_period.load())) {
        [[maybe_unused]] auto const epoch = vars.epoch.load();
        LOG_ERROR("Called snapshot twice in epoch: {}", epoch.native());
        return StakingError::SnapshotInBoundary;
    }

    // 1. Throw out last epoch's snapshot view
    auto valset_snapshot = vars.valset_snapshot;
    while (!valset_snapshot.empty()) {
        u64_be const val_id = valset_snapshot.pop();
        auto snapshot_view = vars.snapshot_view(val_id);
        snapshot_view.stake().clear();
        snapshot_view.commission().clear();
    }

    // 2. Copy the consensus view to the snapshot view
    auto valset_consensus = vars.valset_consensus;
    uint64_t const consensus_valset_length = vars.valset_consensus.length();
    for (uint64_t i = 0; i < consensus_valset_length; ++i) {
        u64_be const val_id = valset_consensus.get(i).load();
        auto snapshot_view = vars.snapshot_view(val_id);
        auto consensus_view = vars.consensus_view(val_id);

        valset_snapshot.push(val_id);
        snapshot_view.stake().store(consensus_view.stake().load());
        snapshot_view.commission().store(consensus_view.commission().load());
    }

    // 3. Throw out the consensus view
    while (!valset_consensus.empty()) {
        u64_be const val_id = valset_consensus.pop();
        auto consensus_view = vars.consensus_view(val_id);
        consensus_view.stake().clear();
        consensus_view.commission().clear();
    }

    // 4. Find all the candidates in the execution set and load into memory for
    // sorting. The only validators selected have OK status. Validators with
    // nonzero status are queued up for removal.
    using Candidate = std::pair<u64_be, uint256_t>;
    std::vector<Candidate> candidates;
    std::vector<uint64_t> removals;

    uint64_t const execution_valset_length = vars.valset_execution.length();
    for (uint64_t i = 0; i < execution_valset_length; ++i) {
        auto const val_id = vars.valset_execution.get(i).load();
        auto val_execution = vars.val_execution(val_id);
        // TODO: once Maged's speculative execution is merged, move this
        // into a separate loop.
        auto const flags = val_execution.get_flags();
        if (MONAD_LIKELY(flags == ValidatorFlagsOk)) {
            uint256_t const stake = val_execution.stake().load().native();
            candidates.emplace_back(val_id, stake);
        }
        else {
            removals.push_back(i);
        }
    }

    // 5. Construct consensus set from top validators
    auto cmp = [](Candidate const &a, Candidate const &b) {
        if (MONAD_LIKELY(a.second != b.second)) {
            // sort by stake descending
            return a.second > b.second;
        }
        // strict ordering: val id ascending
        return a.first.native() < b.first.native();
    };
    uint64_t const n = std::min(candidates.size(), ACTIVE_VALSET_SIZE);
    std::partial_sort(
        candidates.begin(),
        candidates.begin() + static_cast<std::ptrdiff_t>(n),
        candidates.end(),
        cmp);
    for (uint64_t i = 0; i < n; ++i) {
        auto const &[id, stake] = candidates[i];
        valset_consensus.push(id);
        vars.consensus_view(id).stake().store(stake);
        vars.consensus_view(id).commission().store(
            vars.val_execution(id).commission().load());
    }

    // 6. Process removals from execution set to prevent state bloat.
    //
    // Pop-and-swap from the array: highest indices must processed first.
    for (auto it = removals.rbegin(); it != removals.rend(); ++it) {
        auto slot_to_replace = vars.valset_execution.get(*it);
        u64_be const id_to_remove = slot_to_replace.load();
        remove_from_valset(id_to_remove);
        auto const swapped_id = vars.valset_execution.pop();
        slot_to_replace.store(swapped_id);
    }

    vars.in_epoch_delay_period.store(true);

    return outcome::success();
}

// This is a trait for an intrusive linked list in state.
// The delegators are laid out in state as follows:
//      mapping(uint64 /* val */ ) => mapping(Address /* del */ ) => DelInfo
//
// The linked list is designed to support two types of queries:
//   1. validator => List[Delegators]
//   2. delegator => List[Validators]
//
// These are created as doubly linked lists starting at a sentinel address.
// Suppose a delegator at address 0xbeef is delegated with validators 0x1, 0x5,
// and 0xA. For the purposes of this example, let's assume validator ids are one
// byte, meaning the sentinel is 0xff. The list would look like this in state.
// Note that the delegator key is constant.
//
// -------------     -------------    --------------    -------------
// |0xbeef,0xff|  -> |0xbeef,0x01| -> |0xbeef, 0x05| -> |0xbeef,0x0A|
// -------------     -------------    --------------    -------------
//
// The delegator list for a specific validator looks the same
// except the validator is constant.
template <typename Key, typename Ptr>
struct LinkedListTrait;

// Trait for all validators given a delegator
template <>
struct LinkedListTrait<Address, u64_be>
{
    using Key = Address;
    using Ptr = u64_be;

    static constexpr Ptr sentinel()
    {
        return Ptr{0xFFFFFFFFFFFFFFFFull};
    }

    static constexpr Ptr empty()
    {
        return Ptr{};
    }

    static Ptr const &prev(auto const &n)
    {
        return n.iprev;
    }

    static Ptr &prev(auto &n)
    {
        return n.iprev;
    }

    static Ptr const &next(auto const &n)
    {
        return n.inext;
    }

    static Ptr &next(auto &n)
    {
        return n.inext;
    }

    static auto load_node(StakingContract &c, Key const &k, Ptr const &p)
    {
        return c.vars.delegator(p, k).list_node().load(); // storage(id, addr)
    }

    static void
    store_node(StakingContract &c, Key const &k, Ptr const &p, auto const &n)
    {
        c.vars.delegator(p, k).list_node().store(n);
    }
};

// Trait for all delegators given a validator
template <>
struct LinkedListTrait<u64_be, Address>
{
    using Key = u64_be; // val id
    using Ptr = Address; // delegator address

    static constexpr Ptr sentinel()
    {
        return Ptr{{0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF}};
    }

    static constexpr Ptr empty()
    {
        return Ptr{};
    }

    static Ptr const &prev(auto const &n)
    {
        return n.aprev;
    }

    static Ptr &prev(auto &n)
    {
        return n.aprev;
    }

    static Ptr const &next(auto const &n)
    {
        return n.anext;
    }

    static Ptr &next(auto &n)
    {
        return n.anext;
    }

    static auto load_node(StakingContract &c, Key const &k, Ptr const &p)
    {
        return c.vars.delegator(k, p).list_node().load(); // storage(id, addr)
    }

    static void
    store_node(StakingContract &c, Key const &k, Ptr const &p, auto const &n)
    {
        c.vars.delegator(k, p).list_node().store(n);
    }
};

template <typename Key, typename Ptr>
Result<void>
StakingContract::linked_list_insert(Key const &key, Ptr const &this_ptr)
{
    using Trait = LinkedListTrait<Key, Ptr>;

    if (MONAD_UNLIKELY(
            this_ptr == Trait::empty() || this_ptr == Trait::sentinel())) {
        return StakingError::InvalidInput;
    }

    auto this_node = Trait::load_node(*this, key, this_ptr);
    if (Trait::prev(this_node) != Trait::empty()) {
        // all nodes but sentinel have a prev pointer.
        // allows O(1) existence check.
        return outcome::success();
    }

    auto sentinel_node = Trait::load_node(*this, key, Trait::sentinel());
    Ptr const next_ptr = Trait::next(sentinel_node); // may be empty

    if (next_ptr != Trait::empty()) {
        auto next = Trait::load_node(*this, key, next_ptr);
        Trait::prev(next) = this_ptr;
        Trait::store_node(*this, key, next_ptr, next);
    }
    Trait::prev(this_node) = Trait::sentinel();
    Trait::next(this_node) = next_ptr;
    Trait::next(sentinel_node) = this_ptr;

    Trait::store_node(*this, key, this_ptr, this_node);
    Trait::store_node(*this, key, Trait::sentinel(), sentinel_node);

    return outcome::success();
}

template <typename Key, typename Ptr>
void StakingContract::linked_list_remove(Key const &key, Ptr const &this_ptr)
{
    using Trait = LinkedListTrait<Key, Ptr>;

    // These ptr types are blocked during delegator registration. Should never
    // remove them.
    MONAD_ASSERT_THROW(
        this_ptr != Trait::empty() && this_ptr != Trait::sentinel(),
        "invalid list entry");

    auto this_node = Trait::load_node(*this, key, this_ptr);
    if (Trait::prev(this_node) == Trait::empty()) {
        // not in the list
        return;
    }

    Ptr const prev_ptr = Trait::prev(this_node); // may be SENTINEL
    Ptr const next_ptr = Trait::next(this_node); // may be empty

    auto prev_node = Trait::load_node(*this, key, prev_ptr);
    Trait::next(prev_node) = next_ptr;
    Trait::store_node(*this, key, prev_ptr, prev_node);

    if (next_ptr != Trait::empty()) {
        auto next_node = Trait::load_node(*this, key, next_ptr);
        Trait::prev(next_node) = prev_ptr;
        Trait::store_node(*this, key, next_ptr, next_node);
    }

    // remove from list
    Trait::prev(this_node) = Trait::empty();
    Trait::next(this_node) = Trait::empty();
    Trait::store_node(*this, key, this_ptr, this_node);
}

template <typename Key, typename Ptr>
std::tuple<bool, Ptr, std::vector<Ptr>> StakingContract::linked_list_traverse(
    Key const &key, Ptr const &start_ptr, uint32_t const limit)
{
    using Trait = LinkedListTrait<Key, Ptr>;

    Ptr ptr;
    if (start_ptr == Trait::empty()) {
        auto const sentinel_node =
            Trait::load_node(*this, key, Trait::sentinel());
        ptr = Trait::next(sentinel_node);
    }
    else {
        ptr = start_ptr;
    }
    if (MONAD_UNLIKELY(
            Trait::prev(Trait::load_node(*this, key, ptr)) == Trait::empty())) {
        // bogus pointer, not in list.
        return {true, ptr, {}};
    }

    std::vector<Ptr> results;
    uint32_t nodes_read = 0;
    while (ptr != Trait::empty() && nodes_read < limit) {
        auto const node = Trait::load_node(*this, key, ptr);
        results.push_back(std::move(ptr));
        ptr = Trait::next(node);
        ++nodes_read;
    }
    bool const done = (ptr == Trait::empty());
    return {done, ptr, std::move(results)};
}

void StakingContract::emit_log(Receipt::Log const &log)
{
    state_.store_log(log);
    call_tracer_.on_log(log);
}

MONAD_STAKING_NAMESPACE_END
