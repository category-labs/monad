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
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
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

#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>

#include <algorithm>
#include <cstring>
#include <memory>

MONAD_STAKING_ANONYMOUS_NAMESPACE_BEGIN

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

StakingContract::StakingContract(State &state)
    : state_{state}
    , vars{state}
{
}

/////////////
// Events //
/////////////
void StakingContract::emit_validator_created_event(
    u64_be const val_id, Address const &auth_delegator)

{
    constexpr bytes32_t signature{
        0xab6f199d07fd15c571140b120b4b414ab3baa8b5a543b4d4f78c8319d6634974_bytes32};
    auto const event = EventBuilder(STAKING_CA, signature)
                           .add_topic(abi_encode_uint(val_id))
                           .add_topic(abi_encode_address(auth_delegator))
                           .build();
    state_.store_log(event);
}

void StakingContract::emit_validator_status_changed_event(
    u64_be const val_id, u64_be const flags)
{
    constexpr bytes32_t signature{
        0xc95966754e882e03faffaf164883d98986dda088d09471a35f9e55363daf0c53_bytes32};
    auto const event = EventBuilder(STAKING_CA, signature)
                           .add_topic(abi_encode_uint(val_id))
                           .add_data(abi_encode_uint(flags))
                           .build();
    state_.store_log(event);
}

void StakingContract::emit_delegation_event(
    u64_be const val_id, Address const &delegator, u256_be const &amount,
    u64_be const active_epoch)

{
    constexpr bytes32_t signature{
        0xe4d4df1e1827dd28252fd5c3cd7ebccd3da6e0aa31f74c828f3c8542af49d840_bytes32};
    auto const event = EventBuilder(STAKING_CA, signature)
                           .add_topic(abi_encode_uint(val_id))
                           .add_topic(abi_encode_address(delegator))
                           .add_data(abi_encode_uint(amount))
                           .add_data(abi_encode_uint(active_epoch))
                           .build();
    state_.store_log(event);
}

void StakingContract::emit_undelegate_event(
    u64_be const val_id, Address const &delegator, uint8_t withdrawal_id,
    u256_be const &amount, u64_be const activation_epoch)
{
    constexpr bytes32_t signature{
        0x3e53c8b91747e1b72a44894db10f2a45fa632b161fdcdd3a17bd6be5482bac62_bytes32};
    auto const event = EventBuilder(STAKING_CA, signature)
                           .add_topic(abi_encode_uint(val_id))
                           .add_topic(abi_encode_address(delegator))
                           .add_data(abi_encode_uint(withdrawal_id))
                           .add_data(abi_encode_uint(amount))
                           .add_data(abi_encode_uint(activation_epoch))
                           .build();
    state_.store_log(event);
}

void StakingContract::emit_withdraw_event(
    u64_be const val_id, Address const &delegator, uint8_t const withdrawal_id,
    u256_be const &amount)
{
    constexpr bytes32_t signature =
        0x63030e4238e1146c63f38f4ac81b2b23c8be28882e68b03f0887e50d0e9bb18f_bytes32;
    u64_be const withdraw_epoch = vars.epoch.load();
    auto const event = EventBuilder(STAKING_CA, signature)
                           .add_topic(abi_encode_uint(val_id))
                           .add_topic(abi_encode_address(delegator))
                           .add_data(abi_encode_uint(withdrawal_id))
                           .add_data(abi_encode_uint(amount))
                           .add_data(abi_encode_uint(withdraw_epoch))
                           .build();
    state_.store_log(event);
}

void StakingContract::emit_claim_rewards_event(
    u64_be const val_id, Address const &delegator, u256_be const &amount)
{
    constexpr bytes32_t signature{
        0x3170ba953fe3e068954fcbc93913a05bf457825d4d4d86ec9b72ce2186cd8109_bytes32};
    auto const event = EventBuilder(STAKING_CA, signature)
                           .add_topic(abi_encode_uint(val_id))
                           .add_topic(abi_encode_address(delegator))
                           .add_data(abi_encode_uint(amount))
                           .build();
    state_.store_log(event);
}

void StakingContract::emit_commission_changed_event(
    u64_be const val_id, u256_be const &old_commission,
    u256_be const &new_commission)
{
    constexpr bytes32_t signature{
        0xd1698d3454c5b5384b70aaae33f1704af7c7e055f0c75503ba3146dc28995920_bytes32};
    auto const event = EventBuilder(STAKING_CA, signature)
                           .add_topic(abi_encode_uint(val_id))
                           .add_data(abi_encode_uint(old_commission))
                           .add_data(abi_encode_uint(new_commission))
                           .build();
    state_.store_log(event);
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

///////////////////
//  Precompiles  //
///////////////////

std::pair<StakingContract::PrecompileFunc, uint64_t>
StakingContract::precompile_dispatch(byte_string_view &input)
{
    if (MONAD_UNLIKELY(input.size() < 4)) {
        return make_pair(&StakingContract::precompile_fallback, 0);
    }

    auto const signature =
        intx::be::unsafe::load<uint32_t>(input.substr(0, 4).data());
    input.remove_prefix(4);

    using StakingPrecompile = std::pair<PrecompileFunc, uint64_t>;
    constexpr std::array<StakingPrecompile, 26> dispatch_table{
        make_pair(&StakingContract::precompile_fallback, 0),
        make_pair(&StakingContract::precompile_add_validator, 0 /* fixme */),
        make_pair(&StakingContract::precompile_delegate, 0 /* fixme */),
        make_pair(&StakingContract::precompile_undelegate, 0 /* fixme */),
        make_pair(&StakingContract::precompile_compound, 0 /* fixme */),
        make_pair(&StakingContract::precompile_withdraw, 0 /* fixme */),
        make_pair(&StakingContract::precompile_claim_rewards, 0 /* fixme */),
        make_pair(
            &StakingContract::precompile_change_commission, 0 /* fixme */),
        /* reserve space for future upgrades */
        make_pair(&StakingContract::precompile_fallback, 0),
        make_pair(&StakingContract::precompile_fallback, 0),
        make_pair(&StakingContract::precompile_fallback, 0),
        make_pair(&StakingContract::precompile_fallback, 0),
        make_pair(&StakingContract::precompile_fallback, 0),
        make_pair(&StakingContract::precompile_fallback, 0),
        make_pair(&StakingContract::precompile_fallback, 0),
        make_pair(&StakingContract::precompile_fallback, 0),
        make_pair(&StakingContract::precompile_fallback, 0),
        /* getters */
        make_pair(&StakingContract::precompile_get_validator, 0 /* fixme */),
        make_pair(&StakingContract::precompile_get_delegator, 0 /* fixme */),
        make_pair(
            &StakingContract::precompile_get_withdrawal_request, 0 /* fixme */),
        make_pair(
            &StakingContract::precompile_get_consensus_valset, 0 /* fixme */),
        make_pair(
            &StakingContract::precompile_get_snapshot_valset, 0 /* fixme */),
        make_pair(
            &StakingContract::precompile_get_execution_valset, 0 /* fixme */),
        make_pair(
            &StakingContract::precompile_get_validators_for_delegator,
            0 /* fixme */),
        make_pair(
            &StakingContract::precompile_get_delegators_for_validator,
            0 /* fixme */),
        make_pair(&StakingContract::precompile_get_epoch, 0 /* fixme */),
    };

    if (MONAD_UNLIKELY(signature >= dispatch_table.size())) {
        return make_pair(&StakingContract::precompile_fallback, 0);
    }

    return dispatch_table[signature];
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
    byte_string_view const input, evmc_address const &,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    if (MONAD_UNLIKELY(input.size() != sizeof(u64_be) /* validator id */)) {
        return StakingError::InvalidInput;
    }
    auto const val_id = unaligned_load<u64_be>(input.data());
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
    byte_string_view const input, evmc_address const &,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    constexpr size_t MESSAGE_SIZE = sizeof(u64_be) /* validator id */ +
                                    sizeof(Address) /* delegator address */;
    if (MONAD_UNLIKELY(input.size() != MESSAGE_SIZE)) {
        return StakingError::InvalidInput;
    }
    auto const val_id = unaligned_load<u64_be>(input.data());
    auto const address = unaligned_load<Address>(input.data() + sizeof(u64_be));
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
    byte_string_view const input, StorageArray<u64_be> const &valset)
{
    constexpr size_t MESSAGE_SIZE = sizeof(u32_be) /* start index */;
    if (MONAD_UNLIKELY(input.size() != MESSAGE_SIZE)) {
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

    byte_string_view reader = input;
    uint32_t const start_index =
        unaligned_load<u32_be>(consume_bytes(reader, sizeof(u32_be)).data())
            .native();

    auto const [done, next_index, valids] =
        get_valset(valset, start_index, PAGINATED_RESULTS_SIZE);
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

Result<byte_string> StakingContract::precompile_get_validators_for_delegator(
    byte_string_view const input, evmc_address const &,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    constexpr size_t MESSAGE_SIZE = sizeof(Address) /* delegator */ +
                                    sizeof(u64_be) /* start val id to read*/;

    if (MONAD_UNLIKELY(input.size() != MESSAGE_SIZE)) {
        return StakingError::InvalidInput;
    }

    byte_string_view reader = input;
    auto const delegator =
        unaligned_load<Address>(consume_bytes(reader, sizeof(Address)).data());
    auto const start_val_id =
        unaligned_load<u64_be>(consume_bytes(reader, sizeof(u64_be)).data());

    auto const [done, next_val_id, vals_page] = get_validators_for_delegator(
        delegator, start_val_id, PAGINATED_RESULTS_SIZE);

    AbiEncoder encoder;
    encoder.add_bool(done);
    encoder.add_uint(next_val_id);
    encoder.add_uint_array(vals_page);
    return encoder.encode_final();
}

Result<byte_string> StakingContract::precompile_get_delegators_for_validator(
    byte_string_view const input, evmc_address const &,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    constexpr size_t MESSAGE_SIZE =
        sizeof(u64_be) /* validator id */ +
        sizeof(Address) /* start delegator address to read */;

    if (MONAD_UNLIKELY(input.size() != MESSAGE_SIZE)) {
        return StakingError::InvalidInput;
    }

    byte_string_view reader = input;
    auto const val_id =
        unaligned_load<u64_be>(consume_bytes(reader, sizeof(u64_be)).data());
    auto const start_del_addr =
        unaligned_load<Address>(consume_bytes(reader, sizeof(Address)).data());

    auto const [done, next_del_addr, dels_page] = get_delegators_for_validator(
        val_id, start_del_addr, PAGINATED_RESULTS_SIZE);

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
    byte_string_view const input, evmc_address const &,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    constexpr size_t MESSAGE_SIZE = sizeof(u64_be) /* validator id */ +
                                    sizeof(Address) /* delegator */ +
                                    sizeof(uint8_t) /* withdrawal id */;
    if (MONAD_UNLIKELY(input.size() != MESSAGE_SIZE)) {
        return StakingError::InvalidInput;
    }

    byte_string_view reader = input;
    auto const val_id =
        unaligned_load<u64_be>(consume_bytes(reader, sizeof(u64_be)).data());
    auto const delegator =
        unaligned_load<Address>(consume_bytes(reader, sizeof(Address)).data());
    auto const withdrawal_id =
        unaligned_load<uint8_t>(consume_bytes(reader, sizeof(uint8_t)).data());

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
    byte_string_view const input, evmc_address const &,
    evmc_uint256be const &msg_value)
{
    constexpr size_t MESSAGE_SIZE = 33 /* compressed secp pubkey */ +
                                    48 /* compressed bls pubkey */ +
                                    sizeof(Address) /* auth address */ +
                                    sizeof(u256_be) /* signed stake */ +
                                    sizeof(u256_be) /* commission rate */;
    constexpr size_t SIGNATURES_SIZE =
        64 /* secp signature */ + 96 /* bls signature */;

    constexpr size_t EXPECTED_INPUT_SIZE = MESSAGE_SIZE + SIGNATURES_SIZE;

    // Validate input size
    if (MONAD_UNLIKELY(input.size() != EXPECTED_INPUT_SIZE)) {
        return StakingError::InvalidInput;
    }

    // extract individual inputs
    byte_string_view message = input.substr(0, MESSAGE_SIZE);

    byte_string_view reader = input;
    auto const secp_pubkey_serialized =
        unaligned_load<byte_string_fixed<33>>(consume_bytes(reader, 33).data());
    auto const bls_pubkey_serialized =
        unaligned_load<byte_string_fixed<48>>(consume_bytes(reader, 48).data());
    auto const auth_address =
        unaligned_load<Address>(consume_bytes(reader, sizeof(Address)).data());
    auto const signed_stake = unaligned_load<evmc_uint256be>(
        consume_bytes(reader, sizeof(evmc_uint256be)).data());
    auto const commission =
        unaligned_load<u256_be>(consume_bytes(reader, sizeof(u256_be)).data());
    auto const secp_signature_serialized =
        unaligned_load<byte_string_fixed<64>>(consume_bytes(reader, 64).data());
    auto const bls_signature_serialized =
        unaligned_load<byte_string_fixed<96>>(consume_bytes(reader, 96).data());
    if (!reader.empty()) {
        return StakingError::InvalidInput;
    }

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
    Secp256k1Pubkey secp_pubkey(secp_pubkey_serialized);
    if (MONAD_UNLIKELY(!secp_pubkey.is_valid())) {
        return StakingError::InvalidSecpPubkey;
    }
    Secp256k1Signature secp_sig(secp_signature_serialized);
    if (MONAD_UNLIKELY(!secp_sig.is_valid())) {
        return StakingError::InvalidSecpSignature;
    }
    if (MONAD_UNLIKELY(!secp_sig.verify(secp_pubkey, message))) {
        return StakingError::SecpSignatureVerificationFailed;
    }

    // Verify BLS signature
    BlsPubkey bls_pubkey(bls_pubkey_serialized);
    if (MONAD_UNLIKELY(!bls_pubkey.is_valid())) {
        return StakingError::InvalidBlsPubkey;
    }
    BlsSignature bls_sig(bls_signature_serialized);
    if (MONAD_UNLIKELY(!bls_sig.is_valid())) {
        return StakingError::InvalidBlsSignature;
    }
    if (MONAD_UNLIKELY(!bls_sig.verify(bls_pubkey, message))) {
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
        .secp_pubkey = secp_pubkey_serialized,
        .bls_pubkey = bls_pubkey_serialized});
    val.address_flags().store(AddressFlags{
        .auth_address = auth_address, .flags = ValidatorFlagsStakeTooLow});
    val.commission().store(commission);

    emit_validator_created_event(val_id, auth_address);

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
    byte_string_view const input, evmc_address const &msg_sender,
    evmc_uint256be const &msg_value)
{
    // Validate input size
    if (MONAD_UNLIKELY(input.size() != sizeof(u64_be) /* validator id */)) {
        return StakingError::InvalidInput;
    }

    auto const val_id =
        unaligned_load<u64_be>(input.substr(0, sizeof(u64_be)).data());
    auto const stake = intx::be::load<uint256_t>(msg_value);

    if (MONAD_LIKELY(stake != 0)) {
        BOOST_OUTCOME_TRY(delegate(val_id, stake, msg_sender));
    }
    return byte_string{abi_encode_bool(true)};
}

Result<byte_string> StakingContract::precompile_undelegate(
    byte_string_view const input, evmc_address const &msg_sender,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    constexpr size_t MESSAGE_SIZE = sizeof(u64_be) /* validator id */ +
                                    sizeof(u256_be) /* amount */ +
                                    sizeof(uint8_t) /* withdrawal id */;
    if (MONAD_UNLIKELY(input.size() != MESSAGE_SIZE)) {
        return StakingError::InvalidInput;
    }

    byte_string_view reader = input;
    auto const val_id =
        unaligned_load<u64_be>(consume_bytes(reader, sizeof(u64_be)).data());
    uint256_t amount =
        unaligned_load<u256_be>(consume_bytes(reader, sizeof(u256_be)).data())
            .native();
    auto const withdrawal_id =
        unaligned_load<uint8_t>(consume_bytes(reader, sizeof(uint8_t)).data());

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
    byte_string_view const input, evmc_address const &msg_sender,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    constexpr size_t MESSAGE_SIZE = sizeof(u64_be) /* validatorId */;
    if (MONAD_UNLIKELY(input.size() != MESSAGE_SIZE)) {
        return StakingError::InvalidInput;
    }

    auto const val_id =
        unaligned_load<u64_be>(input.substr(0, sizeof(u64_be)).data());

    auto del = vars.delegator(val_id, msg_sender);
    BOOST_OUTCOME_TRY(pull_delegator_up_to_date(val_id, del));
    auto rewards_slot = del.rewards();
    uint256_t const rewards = rewards_slot.load().native();
    rewards_slot.clear();

    if (MONAD_UNLIKELY(rewards != 0)) {
        BOOST_OUTCOME_TRY(delegate(val_id, rewards, msg_sender));
    }

    return byte_string{abi_encode_bool(true)};
}

Result<byte_string> StakingContract::precompile_withdraw(
    byte_string_view const input, evmc_address const &msg_sender,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    constexpr size_t MESSAGE_SIZE =
        sizeof(u64_be) /* validator id */ + sizeof(uint8_t) /* withdrawal id */;
    if (MONAD_UNLIKELY(input.size() != MESSAGE_SIZE)) {
        return StakingError::InvalidInput;
    }

    byte_string_view reader = input;
    auto const val_id =
        unaligned_load<u64_be>(consume_bytes(reader, sizeof(u64_be)).data());
    auto const withdrawal_id =
        unaligned_load<uint8_t>(consume_bytes(reader, sizeof(uint8_t)).data());

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
    byte_string_view const input, evmc_address const &msg_sender,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    constexpr size_t MESSAGE_SIZE = sizeof(u64_be) /* validator id */;
    if (MONAD_UNLIKELY(input.size() != MESSAGE_SIZE)) {
        return StakingError::InvalidInput;
    }
    auto const val_id =
        unaligned_load<u64_be>(input.substr(0, sizeof(u64_be)).data());

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
    byte_string_view const input, evmc_address const &msg_sender,
    evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    constexpr size_t MESSAGE_SIZE =
        sizeof(u64_be) /* validator id */ + sizeof(u256_be) /* commission */;
    if (MONAD_UNLIKELY(input.size() != MESSAGE_SIZE)) {
        return StakingError::InvalidInput;
    }

    byte_string_view reader = input;
    auto const val_id =
        unaligned_load<u64_be>(consume_bytes(reader, sizeof(u64_be)).data());
    auto const new_commission =
        unaligned_load<u256_be>(consume_bytes(reader, sizeof(u256_be)).data());

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
    validator.commission().store(new_commission);
    emit_commission_changed_event(val_id, old_commission, new_commission);

    return byte_string{abi_encode_bool(true)};
}

////////////////////
//  System Calls  //
////////////////////

Result<void>
StakingContract::syscall_on_epoch_change(byte_string_view const input)
{
    if (MONAD_UNLIKELY(input.size() != sizeof(u64_be))) {
        return StakingError::InvalidInput;
    }

    u64_be const next_epoch = unaligned_load<u64_be>(input.data());
    u64_be const next_next_epoch = next_epoch.native() + 1;
    u64_be const last_epoch = vars.epoch.load();
    if (MONAD_UNLIKELY(next_epoch.native() <= last_epoch.native())) {
        LOG_ERROR(
            "Invalid epoch change: from {} to {}",
            last_epoch.native(),
            next_epoch.native());
        return StakingError::InvalidEpochChange;
    }

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
    byte_string_view const input, uint256_t const &raw_reward)
{
    if (MONAD_UNLIKELY(input.size() != sizeof(Address))) {
        return StakingError::InvalidInput;
    }
    auto const block_author = unaligned_load<Address>(input.data());

    // 1. get validator information
    auto const val_id = vars.val_id(block_author).load_checked();
    if (MONAD_UNLIKELY(!val_id.has_value())) {
        return StakingError::BlockAuthorNotInSet;
    }

    // 2. validator must be active
    auto consensus_view = vars.this_epoch_view(val_id.value());
    uint256_t const active_stake = consensus_view.stake().load().native();
    if (MONAD_UNLIKELY(active_stake == 0)) {
        // Validator cannot be in the active set with no stake
        return StakingError::BlockAuthorNotInSet;
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

    // 5. reward wrt to accumulator
    BOOST_OUTCOME_TRY(
        auto const del_reward, checked_sub(raw_reward, commission));
    BOOST_OUTCOME_TRY(
        auto const reward_acc,
        checked_mul_div(del_reward, UNIT_BIAS, active_stake));
    BOOST_OUTCOME_TRY(
        auto const acc,
        checked_add(
            val_execution.accumulated_reward_per_token().load().native(),
            reward_acc));
    val_execution.accumulated_reward_per_token().store(acc);

    // 6. update unclaimed rewards for this validator pool
    BOOST_OUTCOME_TRY(
        auto const unclaimed_rewards,
        checked_add(
            val_execution.unclaimed_rewards().load().native(), del_reward));
    val_execution.unclaimed_rewards().store(unclaimed_rewards);

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

MONAD_STAKING_NAMESPACE_END
