#include <monad/contract/mapping.hpp>
#include <monad/contract/storage_array.hpp>
#include <monad/contract/storage_variable.hpp>
#include <monad/contract/topics.hpp>
#include <monad/core/blake3.hpp>
#include <monad/core/bytes_hash_compare.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/unaligned.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/staking/bls.hpp>
#include <monad/execution/staking/secp256k1.hpp>
#include <monad/execution/staking/types.hpp>
#include <monad/execution/staking_contract.hpp>
#include <monad/state3/state.hpp>

#include <blst.h>
#include <secp256k1.h>

#include <boost/outcome/config.hpp>
// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/generic_code.hpp>
#endif
#include <boost/outcome/success_failure.hpp>

#include <cstring>
#include <memory>
#include <set>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

namespace
{

    byte_string_view
    consume_bytes(byte_string_view &data, size_t const num_bytes)
    {
        byte_string_view ret = data.substr(0, num_bytes);
        data.remove_prefix(num_bytes);
        return ret;
    }

    ///////////////
    //  Staking  //
    ///////////////
    constexpr uint256_t MIN_STAKE_AMOUNT{10e18}; // FIXME
    constexpr uint256_t BASE_STAKING_REWARD{1e18}; // FIXME

    uint256_t increment_id(StorageVariable<uint256_t> &storage)
    {
        auto const id = storage.load().value_or(0);
        storage.store(id + 1);
        return id + 1;
    }

    uint256_t tokens_to_shares(
        uint256_t const &existing_tokens, uint256_t const &existing_shares,
        uint256_t const &new_tokens)
    {
        if (MONAD_UNLIKELY(existing_shares == 0)) {
            return new_tokens;
        }
        else {
            return (new_tokens * existing_shares) / existing_tokens;
        }
    }

    uint256_t shares_to_tokens(
        uint256_t const &existing_tokens, uint256_t const &existing_shares,
        uint256_t const &shares_amount)
    {
        if (MONAD_UNLIKELY(existing_shares == 0)) {
            return 0;
        }
        else {
            return (shares_amount * existing_tokens) / existing_shares;
        }
    }

    //////////////
    //  Crypto  //
    //////////////
    thread_local std::unique_ptr<
        secp256k1_context, decltype(&secp256k1_context_destroy)> const
        secp_context(
            secp256k1_context_create(SECP256K1_CONTEXT_VERIFY),
            &secp256k1_context_destroy);
    constexpr size_t SECP_COMPRESSED_PUBKEY_SIZE{33};
    constexpr size_t SECP_SIGNATURE_SIZE{64};

    constexpr size_t BLS_COMPRESSED_PUBKEY_SIZE{48};
    constexpr size_t BLS_COMPRESSED_SIGNATURE_SIZE{96};
}

StakingContract::StakingContract(State &state, Address const &ca)
    : state_{state}
    , ca_{ca}
    , vars{state, ca}
{
}

StakingContract::Status
StakingContract::precompile_fallback(evmc_message const &)
{
    // Invoked if someone sends money to the contract account. Do nothing and
    // revert.
    return METHOD_NOT_SUPPORTED;
}

StakingContract::Status
StakingContract::precompile_add_validator(evmc_message const &msg)
{
    byte_string_view const input{msg.input_data, msg.input_size};

    constexpr size_t MESSAGE_SIZE = SECP_COMPRESSED_PUBKEY_SIZE +
                                    BLS_COMPRESSED_PUBKEY_SIZE +
                                    sizeof(Address) + sizeof(uint256_t);
    constexpr size_t SIGNATURES_SIZE =
        SECP_SIGNATURE_SIZE + BLS_COMPRESSED_SIGNATURE_SIZE;

    constexpr size_t EXPECTED_INPUT_SIZE = MESSAGE_SIZE + SIGNATURES_SIZE;

    // Validate input size
    if (MONAD_UNLIKELY(input.size() != EXPECTED_INPUT_SIZE)) {
        return INVALID_INPUT;
    }

    // extract individual inputs
    byte_string_view message = input.substr(0, MESSAGE_SIZE);

    byte_string_view reader = input;
    auto const secp_pubkey_serialized = unaligned_load<byte_string_fixed<33>>(
        consume_bytes(reader, SECP_COMPRESSED_PUBKEY_SIZE).data());
    auto const bls_pubkey_serialized = unaligned_load<byte_string_fixed<48>>(
        consume_bytes(reader, BLS_COMPRESSED_PUBKEY_SIZE).data());
    auto const auth_address =
        unaligned_load<Address>(consume_bytes(reader, sizeof(Address)).data());
    auto const signed_stake = intx::be::unsafe::load<uint256_t>(
        consume_bytes(reader, sizeof(uint256_t)).data());
    byte_string_view secp_signature_serialized =
        consume_bytes(reader, SECP_SIGNATURE_SIZE);
    byte_string_view bls_signature_serialized =
        consume_bytes(reader, BLS_COMPRESSED_SIGNATURE_SIZE);
    auto const stake = intx::be::load<uint256_t>(msg.value);

    if (MONAD_UNLIKELY(signed_stake != stake)) {
        return INVALID_INPUT;
    }

    // Verify SECP signature
    Secp256k1_Pubkey secp_pubkey(*secp_context.get(), secp_pubkey_serialized);
    if (MONAD_UNLIKELY(!secp_pubkey.is_valid())) {
        return INVALID_SECP_PUBKEY;
    }
    Secp256k1_Signature secp_sig(
        *secp_context.get(), secp_signature_serialized);
    if (MONAD_UNLIKELY(!secp_sig.is_valid())) {
        return INVALID_SECP_SIGNATURE;
    }
    if (MONAD_UNLIKELY(!secp_sig.verify(secp_pubkey, message))) {
        return SECP_SIGNATURE_VERIFICATION_FAILED;
    }

    // Verify BLS signature
    Bls_Pubkey bls_pubkey(bls_pubkey_serialized);
    if (MONAD_UNLIKELY(!bls_pubkey.is_valid())) {
        return INVALID_BLS_PUBKEY;
    }
    Bls_Signature bls_sig(bls_signature_serialized);
    if (MONAD_UNLIKELY(!bls_sig.is_valid())) {
        return INVALID_BLS_SIGNATURE;
    }
    if (MONAD_UNLIKELY(!bls_sig.verify(bls_pubkey, message))) {
        return BLS_SIGNATURE_VERIFICATION_FAILED;
    }

    // Check if validator already exists
    Address const address = address_from_secpkey(secp_pubkey.serialize());
    auto validator_id_storage = vars.validator_id(address);
    auto validator_id_bls_storage =
        vars.validator_id_bls(bls_pubkey_serialized);
    if (MONAD_UNLIKELY(
            validator_id_storage.load().has_value() ||
            validator_id_bls_storage.load().has_value())) {
        return VALIDATOR_EXISTS;
    }

    uint256_t const validator_id = increment_id(vars.last_validator_id);
    validator_id_storage.store(validator_id);
    validator_id_bls_storage.store(validator_id);

    vars.validator_info(validator_id)
        .store(ValidatorInfo{
            .auth_address = auth_address,
            .bls_pubkey = bls_pubkey_serialized,
            .total_stake = 0,
            .active_stake = 0,
            .active_shares = 0,
            .activating_stake = 0,
            .deactivating_shares = 0,
            .rewards = {}});

    vars.validator_set.push(validator_id);

    // state_.store_log(
    //     Receipt::Log{
    //         .data = byte_string{secp_pubkey_serialized} +
    //                 byte_string{bls_pubkey_serialized},
    //         .topics = create_topics(
    //             "AddValidator(bytes32,address,bytes,bytes)",
    //             validator_id,
    //             address),
    //         .address = ca_});

    return add_stake(validator_id, stake, msg.sender);
}

StakingContract::Status StakingContract::add_stake(
    uint256_t const &validator_id, uint256_t const &amount,
    Address const &delegator)
{
    if (MONAD_UNLIKELY(amount < MIN_STAKE_AMOUNT)) {
        return MINIMUM_STAKE_NOT_MET;
    }

    auto valinfo_slot = vars.validator_info(validator_id);
    auto valinfo = valinfo_slot.load();
    if (MONAD_UNLIKELY(!valinfo.has_value())) {
        return UNKNOWN_VALIDATOR;
    }

    auto delinfo_slot = vars.delegator_info(validator_id, delegator);
    auto delinfo = delinfo_slot.load();

    uint256_t const epoch = vars.epoch.load().value_or(0);

    uint256_t const deposit_id = increment_id(vars.last_deposit_request_id);
    vars.deposit_queue(epoch).push(deposit_id);
    vars.deposit_request(deposit_id)
        .store(DepositRequest{
            .validator_id = validator_id,
            .amount = amount,
            .delegator = delegator});

    delinfo->activating_stake += amount;
    valinfo->activating_stake += amount;
    delinfo_slot.store(delinfo.value());
    valinfo_slot.store(valinfo.value());

    return SUCCESS;
}

StakingContract::Status
StakingContract::precompile_add_stake(evmc_message const &msg)
{
    byte_string_view const input{msg.input_data, msg.input_size};

    // Validate input size
    if (MONAD_UNLIKELY(input.size() != sizeof(uint256_t))) {
        return INVALID_INPUT;
    }

    auto const stake = intx::be::load<uint256_t>(msg.value);
    uint256_t const validator_id = intx::be::unsafe::load<uint256_t>(
        input.substr(0, sizeof(uint256_t)).data());
    return add_stake(validator_id, stake, msg.sender);
}

StakingContract::Status
StakingContract::precompile_remove_stake(evmc_message const &msg)
{
    byte_string_view const input{msg.input_data, msg.input_size};

    constexpr size_t MESSAGE_SIZE =
        sizeof(uint256_t) /* validatorId */ + sizeof(uint256_t) /* amount */;
    if (MONAD_UNLIKELY(input.size() != MESSAGE_SIZE)) {
        return INVALID_INPUT;
    }
    uint256_t const validator_id = intx::be::unsafe::load<uint256_t>(
        input.substr(0, sizeof(uint256_t)).data());
    uint256_t const shares = intx::be::unsafe::load<uint256_t>(
        input.substr(sizeof(uint256_t), sizeof(uint256_t)).data());

    auto valinfo_slot = vars.validator_info(validator_id);
    auto valinfo = valinfo_slot.load();
    if (MONAD_UNLIKELY(!valinfo.has_value())) {
        return UNKNOWN_VALIDATOR;
    }

    auto delinfo_slot = vars.delegator_info(validator_id, msg.sender);
    auto delinfo = delinfo_slot.load();
    if (MONAD_UNLIKELY(delinfo.has_value())) {
        return UNKNOWN_DELEGATOR;
    }

    // enough shares?
    if (MONAD_UNLIKELY(delinfo->active_shares < shares)) {
        return NOT_ENOUGH_SHARES_TO_WITHDRAW;
    }

    uint256_t const withdrawal_id =
        increment_id(vars.last_withdrawal_request_id);

    uint256_t const epoch = vars.epoch.load().value_or(0);

    vars.withdrawal_queue(epoch).push(withdrawal_id);
    vars.withdrawal_request(withdrawal_id)
        .store(WithdrawalRequest{
            .validator_id = validator_id,
            .shares = shares,
            .delegator = msg.sender});

    delinfo->deactivating_shares += shares;
    valinfo->deactivating_shares += shares;
    delinfo_slot.store(delinfo.value());
    valinfo_slot.store(valinfo.value());

    return SUCCESS;
}

Result<void> StakingContract::syscall_reward_validator(
    byte_string_fixed<33> const &beneficiary)
{
    Secp256k1_Pubkey pubkey(*secp_context.get(), beneficiary);
    if (MONAD_UNLIKELY(!pubkey.is_valid())) {
        return StakingSyscallError::InvalidValidatorSecpKey;
    }

    Address const address = address_from_secpkey(pubkey.serialize());
    auto const validator_id = vars.validator_id(address).load();
    if (MONAD_UNLIKELY(validator_id.has_value())) {
        return StakingSyscallError::RewardValidatorNotInSet;
    }

    auto validator_info_storage = vars.validator_info(validator_id.value());
    auto validator_info = validator_info_storage.load();
    if (MONAD_UNLIKELY(!validator_info.has_value())) {
        return StakingSyscallError::InvalidState;
    }

    state_.add_to_balance(ca_, BASE_STAKING_REWARD);
    validator_info->rewards[1] += BASE_STAKING_REWARD;
    validator_info_storage.store(validator_info.value());

    return success();
}

Result<void> StakingContract::syscall_on_epoch_change()
{
    auto const maybe_epoch = vars.epoch.load();
    if (MONAD_UNLIKELY(!maybe_epoch.has_value())) {
        return success();
    }
    uint256_t const epoch = maybe_epoch.value();

    // 1. Apply staking rewards
    std::unordered_map<uint256_t, uint256_t, BytesHashCompare<uint256_t>>
        val_id_to_index;
    uint256_t const num_validators = vars.validator_set.length();
    for (uint256_t i = 0; i < num_validators; i += 1) {
        auto const validator_id_storage = vars.validator_set.get(i);
        auto const validator_id = validator_id_storage.load();
        if (MONAD_UNLIKELY(!validator_id.has_value())) {
            return StakingSyscallError::InvalidState;
        }

        val_id_to_index[validator_id.value()] = i;

        auto valinfo_storage = vars.validator_info(validator_id.value());
        auto valinfo = valinfo_storage.load();
        if (MONAD_UNLIKELY(!valinfo.has_value())) {
            return StakingSyscallError::InvalidState;
        }

        // TODO: apply commission rate
        valinfo->total_stake += valinfo->rewards[0];
        valinfo->active_stake += valinfo->rewards[0];
        valinfo->rewards[0] = valinfo->rewards[1];
        valinfo->rewards[1] = 0;
        valinfo_storage.store(valinfo.value());
    }

    // 2. Apply deposits
    StorageArray<uint256_t> deposit_queue_storage = vars.deposit_queue(epoch);
    uint256_t const num_deposits = deposit_queue_storage.length();
    for (uint256_t i = 0; i < num_deposits; i += 1) {
        auto deposit_id = deposit_queue_storage.pop();
        auto deposit_request_storage = vars.deposit_request(deposit_id);
        auto deposit_request = deposit_request_storage.load();
        if (MONAD_UNLIKELY(!deposit_request.has_value())) {
            return StakingSyscallError::InvalidState;
        }

        auto valinfo_storage =
            vars.validator_info(deposit_request->validator_id);
        auto valinfo = valinfo_storage.load();
        if (MONAD_UNLIKELY(!valinfo.has_value())) {
            return StakingSyscallError::InvalidState;
        }

        auto delinfo_storage = vars.delegator_info(
            deposit_request->validator_id, deposit_request->delegator);
        auto delinfo = delinfo_storage.load();
        if (MONAD_UNLIKELY(!delinfo.has_value())) {
            return StakingSyscallError::InvalidState;
        }

        uint256_t const shares_to_mint = tokens_to_shares(
            valinfo->active_stake,
            valinfo->active_shares,
            deposit_request->amount);

        valinfo->active_stake += deposit_request->amount;
        valinfo->active_shares += shares_to_mint;

        delinfo->active_shares += shares_to_mint;

        valinfo_storage.store(valinfo.value());
        delinfo_storage.store(delinfo.value());

        deposit_request_storage.clear();
    }
    if (MONAD_UNLIKELY(deposit_queue_storage.length() != 0)) {
        return StakingSyscallError::CouldNotClearStorage;
    }

    // 3. Apply withdrawal requests
    StorageArray<uint256_t> withdrawal_queue_storage =
        vars.withdrawal_queue(epoch);
    uint256_t const num_withdrawals = withdrawal_queue_storage.length();
    std::set<uint256_t, std::greater<uint256_t>> valset_removals;
    for (uint256_t i = 0; i < num_withdrawals; i += 1) {
        auto withdrawal_id = withdrawal_queue_storage.pop();
        auto withdrawal_request_storage =
            vars.withdrawal_request(withdrawal_id);
        auto withdrawal_request = withdrawal_request_storage.load();
        if (MONAD_UNLIKELY(!withdrawal_request.has_value())) {
            return StakingSyscallError::InvalidState;
        }

        auto valinfo_storage =
            vars.validator_info(withdrawal_request->validator_id);
        auto valinfo = valinfo_storage.load();
        if (MONAD_UNLIKELY(!valinfo.has_value())) {
            return StakingSyscallError::InvalidState;
        }

        auto delinfo_storage = vars.delegator_info(
            withdrawal_request->validator_id, withdrawal_request->delegator);
        auto delinfo = delinfo_storage.load();
        if (MONAD_UNLIKELY(!delinfo.has_value())) {
            return StakingSyscallError::InvalidState;
        }

        uint256_t const tokens_to_burn = shares_to_tokens(
            valinfo->active_stake,
            valinfo->active_shares,
            withdrawal_request->shares);

        valinfo->active_stake -= tokens_to_burn;
        valinfo->active_shares -= withdrawal_request->shares;

        delinfo->balance += tokens_to_burn;
        delinfo->active_shares -= withdrawal_request->shares;

        if (withdrawal_request->delegator == valinfo->auth_address) {
            auto const tokens_after_withdrawal = shares_to_tokens(
                valinfo->active_stake,
                valinfo->active_shares,
                delinfo->active_shares);
            if (MONAD_LIKELY(tokens_after_withdrawal < MIN_STAKE_AMOUNT)) {
                valset_removals.insert(
                    val_id_to_index[withdrawal_request->validator_id]);
            }
        }

        valinfo_storage.store(valinfo.value());
        delinfo_storage.store(delinfo.value());

        withdrawal_request_storage.clear();
    }
    if (MONAD_UNLIKELY(withdrawal_queue_storage.length() != 0)) {
        return StakingSyscallError::CouldNotClearStorage;
    }

    for (auto const &removal : valset_removals) {
        auto to_remove = vars.validator_set.get(removal);
        uint256_t const id = vars.validator_set.pop();
        to_remove.store(id);
    }

    return success();
}

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::StakingSyscallError>::mapping> const &
quick_status_code_from_enum<monad::StakingSyscallError>::value_mappings()
{
    using monad::StakingSyscallError;

    static std::initializer_list<mapping> const v = {
        {StakingSyscallError::Success, "success", {errc::success}},
        {StakingSyscallError::InvalidValidatorSecpKey,
         "invalid secp pubkey",
         {}},
        {StakingSyscallError::InvalidState, "invalid state", {}},
        {StakingSyscallError::RewardValidatorNotInSet,
         "rewarding validator not in set",
         {}},
        {StakingSyscallError::CouldNotClearStorage,
         "Could not clear storage",
         {}}};
    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
