#include <monad/contract/mapping.hpp>
#include <monad/contract/storage_array.hpp>
#include <monad/contract/storage_variable.hpp>
#include <monad/contract/topics.hpp>
#include <monad/core/blake3.hpp>
#include <monad/core/byte_string.hpp>
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

    Uint256Native tokens_to_shares(
        Uint256Native const &existing_tokens,
        Uint256Native const &existing_shares, Uint256Native const &new_tokens)
    {
        if (MONAD_UNLIKELY(existing_shares == 0)) {
            return new_tokens;
        }
        else {
            return (new_tokens * existing_shares) / existing_tokens;
        }
    }

    Uint256Native shares_to_tokens(
        Uint256Native const &existing_tokens,
        Uint256Native const &existing_shares,
        Uint256Native const &shares_amount)
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

std::pair<StakingContract::PrecompileFunc, uint64_t>
StakingContract::precompile_dispatch(byte_string_view &input)
{
    if (MONAD_UNLIKELY(input.size() < 4)) {
        return make_pair(&StakingContract::precompile_fallback, 0);
    }

    auto const signature =
        intx::be::unsafe::load<uint32_t>(input.substr(0, 4).data());
    input.remove_prefix(4);

    switch (signature) {
    case 0x0d809fd3:
        return make_pair(
            &StakingContract::precompile_get_validator_info, 0 /* fixme */);
    case 0xc7a52e25:
        return make_pair(
            &StakingContract::precompile_add_validator, 0 /* fixme */);
    case 0x91b3006c:
        return make_pair(&StakingContract::precompile_add_stake, 0 /* fixme */);
    case 0x1b3a5c4c:
        return make_pair(
            &StakingContract::precompile_remove_stake, 0 /* fixme */);
    default:
        return make_pair(&StakingContract::precompile_fallback, 0);
    }
}

StakingContract::Output StakingContract::precompile_get_validator_info(
    byte_string_view const input, evmc_address const &, evmc_uint256be const &)
{
    if (MONAD_UNLIKELY(input.size() != sizeof(Uint256BE))) {
        return INVALID_INPUT;
    }
    auto const validator_id = unaligned_load<Uint256BE>(input.data());
    auto const valinfo = vars.validator_info(validator_id).load_unchecked();
    return Output(SUCCESS, abi_encode_validator_info(valinfo));
}

StakingContract::Output StakingContract::precompile_fallback(
    byte_string_view const, evmc_address const &, evmc_uint256be const &)
{
    return METHOD_NOT_SUPPORTED;
}

StakingContract::Output StakingContract::precompile_add_validator(
    byte_string_view const input, evmc_address const &,
    evmc_uint256be const &msg_value)
{
    constexpr size_t MESSAGE_SIZE = SECP_COMPRESSED_PUBKEY_SIZE +
                                    BLS_COMPRESSED_PUBKEY_SIZE +
                                    sizeof(Address) + sizeof(Uint256BE);
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
    auto const signed_stake = unaligned_load<evmc_uint256be>(
        consume_bytes(reader, sizeof(evmc_uint256be)).data());
    auto const secp_signature_serialized =
        unaligned_load<byte_string_fixed<64>>(
            consume_bytes(reader, SECP_SIGNATURE_SIZE).data());
    auto const bls_signature_serialized = unaligned_load<byte_string_fixed<96>>(
        consume_bytes(reader, BLS_COMPRESSED_SIGNATURE_SIZE).data());
    if (!reader.empty()) {
        return INVALID_INPUT;
    }

    if (MONAD_UNLIKELY(
            0 !=
            memcmp(
                signed_stake.bytes, msg_value.bytes, sizeof(evmc_uint256be)))) {
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
    auto const address = address_from_secpkey(secp_pubkey.serialize());
    auto validator_id_storage = vars.validator_id(address);
    auto validator_id_bls_storage =
        vars.validator_id_bls(bls_pubkey_serialized);
    if (MONAD_UNLIKELY(
            validator_id_storage.load().has_value() ||
            validator_id_bls_storage.load().has_value())) {
        return VALIDATOR_EXISTS;
    }

    auto const validator_id =
        vars.last_validator_id.load_unchecked().native().add(1).to_be();
    validator_id_storage.store(validator_id);
    validator_id_bls_storage.store(validator_id);
    vars.last_validator_id.store(validator_id);

    vars.validator_info(validator_id)
        .store(ValidatorInfo{
            .auth_address = auth_address,
            .bls_pubkey = bls_pubkey_serialized,
            .active_stake = {},
            .active_shares = {},
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

    return add_stake(validator_id, msg_value, auth_address);
}

StakingContract::Output StakingContract::add_stake(
    Uint256BE const &validator_id, Uint256BE const &amount,
    Address const &delegator)
{
    if (MONAD_UNLIKELY(amount.native() < MIN_STAKE_AMOUNT)) {
        return MINIMUM_STAKE_NOT_MET;
    }

    if (MONAD_UNLIKELY(!vars.validator_info(validator_id).load().has_value())) {
        return UNKNOWN_VALIDATOR;
    }

    auto const deposit_id =
        vars.last_deposit_request_id.load_unchecked().native().add(1).to_be();
    vars.last_deposit_request_id.store(deposit_id);
    vars.deposit_queue(vars.epoch.load_unchecked().native().add(2).to_be())
        .push(deposit_id);
    vars.deposit_request(deposit_id)
        .store(DepositRequest{
            .validator_id = validator_id,
            .delegator = delegator,
            .amount = amount});
    return SUCCESS;
}

StakingContract::Output StakingContract::precompile_add_stake(
    byte_string_view const input, evmc_address const &msg_sender,
    evmc_uint256be const &msg_value)
{
    constexpr size_t MESSAGE_SIZE = sizeof(Uint256BE) /* validatorId */;

    // Validate input size
    if (MONAD_UNLIKELY(input.size() != MESSAGE_SIZE)) {
        return INVALID_INPUT;
    }

    auto const validator_id =
        unaligned_load<Uint256BE>(input.substr(0, sizeof(Uint256BE)).data());
    return add_stake(validator_id, Uint256BE{msg_value}, msg_sender);
}

StakingContract::Output StakingContract::precompile_remove_stake(
    byte_string_view const input, evmc_address const &msg_sender,
    evmc_uint256be const &)
{
    constexpr size_t MESSAGE_SIZE =
        sizeof(Uint256BE) /* validatorId */ + sizeof(Uint256BE) /* amount */;
    if (MONAD_UNLIKELY(input.size() != MESSAGE_SIZE)) {
        return INVALID_INPUT;
    }
    auto const validator_id =
        unaligned_load<Uint256BE>(input.substr(0, sizeof(Uint256BE)).data());
    auto const shares = unaligned_load<Uint256BE>(
        input.substr(sizeof(Uint256BE), sizeof(Uint256BE)).data());

    if (MONAD_UNLIKELY(!vars.validator_info(validator_id).load().has_value())) {
        return UNKNOWN_VALIDATOR;
    }

    auto const delinfo = vars.delegator_info(validator_id, msg_sender).load();
    if (MONAD_UNLIKELY(!delinfo.has_value())) {
        return UNKNOWN_DELEGATOR;
    }

    // enough shares?
    if (MONAD_UNLIKELY(delinfo->active_shares.native() < shares.native())) {
        return NOT_ENOUGH_SHARES_TO_WITHDRAW;
    }

    auto const withdrawal_id = vars.last_withdrawal_request_id.load_unchecked()
                                   .native()
                                   .add(1)
                                   .to_be();
    vars.last_withdrawal_request_id.store(withdrawal_id);
    vars.withdrawal_queue(vars.epoch.load_unchecked().native().add(2).to_be())
        .push(withdrawal_id);
    vars.withdrawal_request(withdrawal_id)
        .store(WithdrawalRequest{
            .validator_id = validator_id,
            .delegator = msg_sender,
            .shares = shares});

    return SUCCESS;
}

Result<void>
StakingContract::syscall_reward_validator(Address const &block_author)
{
    auto const validator_id = vars.validator_id(block_author).load();
    if (MONAD_UNLIKELY(!validator_id.has_value())) {
        return StakingSyscallError::BlockAuthorNotInSet;
    }

    auto validator_info_storage = vars.validator_info(validator_id.value());
    auto validator_info = validator_info_storage.load();
    if (MONAD_UNLIKELY(!validator_info.has_value())) {
        return StakingSyscallError::InvalidState;
    }

    state_.add_to_balance(ca_, BASE_STAKING_REWARD);
    validator_info->rewards[1] =
        validator_info->rewards[1].native().add(BASE_STAKING_REWARD).to_be();
    validator_info_storage.store(validator_info.value());

    return success();
}

Result<void> StakingContract::syscall_on_epoch_change()
{
    auto const maybe_epoch = vars.epoch.load();
    if (MONAD_UNLIKELY(!maybe_epoch.has_value())) {
        return success();
    }
    auto const epoch = maybe_epoch.value();

    // 1. Apply staking rewards
    std::unordered_map<Uint256BE, uint256_t, BytesHashCompare<Uint256BE>>
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
        valinfo->active_stake = valinfo->active_stake.native()
                                    .add(valinfo->rewards[0].native())
                                    .to_be();
        valinfo->rewards[0] = valinfo->rewards[1];
        valinfo->rewards[1] = Uint256BE{};
        valinfo_storage.store(valinfo.value());
    }

    // 2. Apply withdrawal requests
    auto withdrawal_queue_storage = vars.withdrawal_queue(epoch);
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
        auto delinfo = delinfo_storage.load_unchecked();

        auto val_active_stake = valinfo->active_stake.native();
        auto val_active_shares = valinfo->active_shares.native();
        auto const withdrawal_shares = withdrawal_request->shares.native();

        auto const tokens_to_burn = shares_to_tokens(
            val_active_stake, val_active_shares, withdrawal_shares);

        valinfo->active_stake = val_active_stake.sub(tokens_to_burn).to_be();
        valinfo->active_shares =
            val_active_shares.sub(withdrawal_shares).to_be();

        delinfo.balance = delinfo.balance.native().add(tokens_to_burn).to_be();
        delinfo.active_shares =
            delinfo.active_shares.native().sub(withdrawal_shares).to_be();

        if (withdrawal_request->delegator == valinfo->auth_address) {
            auto const tokens_after_withdrawal = shares_to_tokens(
                val_active_stake,
                val_active_shares,
                delinfo.active_shares.native());
            if (MONAD_LIKELY(tokens_after_withdrawal < MIN_STAKE_AMOUNT)) {
                valset_removals.insert(
                    val_id_to_index[withdrawal_request->validator_id]);
            }
        }

        valinfo_storage.store(valinfo.value());
        delinfo_storage.store(delinfo);

        withdrawal_request_storage.clear();
    }
    if (MONAD_UNLIKELY(withdrawal_queue_storage.length() != 0)) {
        return StakingSyscallError::CouldNotClearStorage;
    }

    // 3. Apply deposit requests
    auto deposit_queue_storage = vars.deposit_queue(epoch);
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
        auto delinfo = delinfo_storage.load_unchecked();

        auto val_active_stake = valinfo->active_stake.native();
        auto val_active_shares = valinfo->active_shares.native();
        auto const deposit_amount = deposit_request->amount.native();

        auto const shares_to_mint = tokens_to_shares(
            val_active_stake, val_active_shares, deposit_amount);

        valinfo->active_stake = val_active_stake.add(deposit_amount).to_be();
        valinfo->active_shares = val_active_shares.add(shares_to_mint).to_be();
        delinfo.active_shares =
            delinfo.active_shares.native().add(shares_to_mint).to_be();

        valinfo_storage.store(valinfo.value());
        delinfo_storage.store(delinfo);

        deposit_request_storage.clear();
    }
    if (MONAD_UNLIKELY(deposit_queue_storage.length() != 0)) {
        return StakingSyscallError::CouldNotClearStorage;
    }

    for (auto const &removal : valset_removals) {
        auto to_remove = vars.validator_set.get(removal);
        auto const id = vars.validator_set.pop();
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
        {StakingSyscallError::BlockAuthorNotInSet,
         "block author not in validator set",
         {}},
        {StakingSyscallError::CouldNotClearStorage,
         "Could not clear storage",
         {}}};
    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
