#include <monad/contract/mapping.hpp>
#include <monad/contract/storage_array.hpp>
#include <monad/contract/storage_variable.hpp>
#include <monad/core/blake3.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/unaligned.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/staking/bls.hpp>
#include <monad/execution/staking/secp256k1.hpp>
#include <monad/execution/staking/types.hpp>
#include <monad/execution/staking_contract.hpp>
#include <monad/state3/state.hpp>

#include <cstring>
#include <memory>

#include <blst.h>
#include <secp256k1.h>

MONAD_NAMESPACE_BEGIN

namespace
{

    byte_string_view read_bytes(byte_string_view &data, size_t const num_bytes)
    {
        byte_string_view ret = data.substr(0, num_bytes);
        data.remove_prefix(num_bytes);
        return ret;
    }

    //////////////////////
    //     Staking     //
    //////////////////////
    constexpr uint256_t MIN_STAKE_AMOUNT{1e18}; // 1 MON

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

    //////////////////////
    //      Crypto      //
    //////////////////////
    constexpr size_t SECP_COMPRESSED_PUBKEY_SIZE{33};
    constexpr size_t SECP_SIGNATURE_SIZE{64};

    constexpr size_t BLS_COMPRESSED_PUBKEY_SIZE{48};
    constexpr size_t BLS_COMPRESSED_SIGNATURE_SIZE{96};
}

StakingContract::StakingContract(
    State &state, Address const &ca, uint64_t const epoch)
    : state_{state}
    , epoch_{epoch}
    , vars{state, ca}
{
}

evmc_status_code StakingContract::add_validator(
    byte_string_view const input, evmc_message const &)
{
    constexpr size_t MESSAGE_SIZE = SECP_COMPRESSED_PUBKEY_SIZE +
                                    BLS_COMPRESSED_PUBKEY_SIZE +
                                    sizeof(Address);
    constexpr size_t SIGNATURES_SIZE =
        SECP_SIGNATURE_SIZE + BLS_COMPRESSED_SIGNATURE_SIZE;

    constexpr size_t EXPECTED_INPUT_SIZE = MESSAGE_SIZE + SIGNATURES_SIZE;

    // Validate input size
    if (MONAD_UNLIKELY(input.size() != EXPECTED_INPUT_SIZE)) {
        return EVMC_REVERT;
    }

    // extract individual inputs
    byte_string_view message = input.substr(0, MESSAGE_SIZE);

    byte_string_view reader = input;
    byte_string_view secp_pubkey_serialized =
        read_bytes(reader, SECP_COMPRESSED_PUBKEY_SIZE);
    byte_string_view bls_pubkey_serialized =
        read_bytes(reader, BLS_COMPRESSED_PUBKEY_SIZE);
    byte_string_view auth_address = read_bytes(reader, sizeof(Address));
    byte_string_view secp_signature_serialized =
        read_bytes(reader, SECP_SIGNATURE_SIZE);
    byte_string_view bls_signature_serialized =
        read_bytes(reader, BLS_COMPRESSED_SIGNATURE_SIZE);

    thread_local std::unique_ptr<
        secp256k1_context,
        decltype(&secp256k1_context_destroy)> const
        context(
            secp256k1_context_create(SECP256K1_CONTEXT_VERIFY),
            &secp256k1_context_destroy);

    // Verify SECP signature
    Secp256k1_Pubkey secp_pubkey(*context.get(), secp_pubkey_serialized);
    if (MONAD_UNLIKELY(!secp_pubkey.is_valid())) {
        return EVMC_REVERT;
    }
    Secp256k1_Signature secp_sig(*context.get(), secp_signature_serialized);
    if (MONAD_UNLIKELY(!secp_sig.is_valid())) {
        return EVMC_REVERT;
    }
    if (MONAD_UNLIKELY(!secp_sig.verify(secp_pubkey, message))) {
        return EVMC_REVERT;
    }

    // Verify BLS signature
    Bls_Pubkey bls_pubkey(bls_pubkey_serialized);
    if (MONAD_UNLIKELY(!bls_pubkey.is_valid())) {
        return EVMC_REVERT;
    }
    Bls_Signature bls_sig(bls_signature_serialized);
    if (MONAD_UNLIKELY(!bls_sig.is_valid())) {
        return EVMC_REVERT;
    }
    if (MONAD_UNLIKELY(!bls_sig.verify(bls_pubkey, message))) {
        return EVMC_REVERT;
    }

    uint256_t const validator_id = increment_id(vars.last_validator_id);

    Address const address = address_from_secpkey(secp_pubkey.serialize());
    vars.validator_id(address).store(validator_id);

    vars.validator_info(validator_id)
        .store(ValidatorInfo{
            .auth_address = unaligned_load<Address>(auth_address.data()),
            .bls_pubkey = unaligned_load<byte_string_fixed<48>>(
                bls_pubkey_serialized.data()),
            .total_stake = 0,
            .active_stake = 0,
            .active_shares = 0,
            .activating_stake = 0,
            .deactivating_shares = 0,
            .epoch_rewards = 0});

    vars.validator_set.push(validator_id);

    return EVMC_SUCCESS;
}

evmc_status_code StakingContract::add_stake(
    byte_string_view const input, evmc_message const &msg)
{
    // Validate input size
    if (MONAD_UNLIKELY(input.size() != sizeof(uint256_t))) {
        return EVMC_REVERT;
    }

    auto const stake = intx::be::load<uint256_t>(msg.value);
    if (MONAD_UNLIKELY(stake < MIN_STAKE_AMOUNT)) {
        return EVMC_REVERT;
    }

    uint256_t const validator_id = intx::be::unsafe::load<uint256_t>(
        input.substr(0, sizeof(uint256_t)).data());

    auto valinfo_slot = vars.validator_info(validator_id);
    auto valinfo = valinfo_slot.load();
    if (MONAD_UNLIKELY(!valinfo.has_value())) {
        return EVMC_REVERT;
    }

    auto delinfo_slot = vars.delegator_info(validator_id, msg.sender);
    auto delinfo = delinfo_slot.load();

    uint256_t const deposit_id = increment_id(vars.last_deposit_request_id);
    vars.deposit_queue(epoch_ + 2).push(deposit_id);
    vars.deposit_request(deposit_id)
        .store(DepositRequest{
            .validator_id = validator_id,
            .amount = stake,
            .delegator = msg.sender});

    delinfo->activating_stake += stake;
    valinfo->activating_stake += stake;
    delinfo_slot.store(delinfo.value());
    valinfo_slot.store(valinfo.value());

    return EVMC_SUCCESS;
}

evmc_status_code StakingContract::remove_stake(
    byte_string_view const input, evmc_message const &msg)
{
    constexpr size_t MESSAGE_SIZE =
        sizeof(uint256_t) /* validatorId */ + sizeof(uint256_t) /* amount */;
    if (MONAD_UNLIKELY(input.size()) != MESSAGE_SIZE) {
        return EVMC_REVERT;
    }
    uint256_t const validator_id = intx::be::unsafe::load<uint256_t>(
        input.substr(0, sizeof(uint256_t)).data());
    uint256_t const shares = intx::be::unsafe::load<uint256_t>(
        input.substr(sizeof(uint256_t), sizeof(uint256_t)).data());

    auto valinfo_slot = vars.validator_info(validator_id);
    auto valinfo = valinfo_slot.load();
    if (MONAD_UNLIKELY(!valinfo.has_value())) {
        return EVMC_REVERT;
    }

    auto delinfo_slot = vars.delegator_info(validator_id, msg.sender);
    auto delinfo = delinfo_slot.load();
    if (MONAD_UNLIKELY(delinfo.has_value())) {
        return EVMC_REVERT;
    }

    uint256_t const withdrawal_id =
        increment_id(vars.last_withdrawal_request_id);

    vars.withdrawal_queue(epoch_ + 2).push(withdrawal_id);
    vars.withdrawal_request(withdrawal_id)
        .store(WithdrawalRequest{
            .validator_id = validator_id,
            .shares = shares,
            .delegator = msg.sender});

    delinfo->deactivating_shares += shares;
    valinfo->deactivating_shares += shares;
    delinfo_slot.store(delinfo.value());
    valinfo_slot.store(valinfo.value());

    return EVMC_SUCCESS;
}

void StakingContract::on_epoch_change()
{
    // 1. Apply staking rewards
    uint256_t const num_validators = vars.validator_set.length();
    for (uint256_t i = 0; i < num_validators; i += 1) {
        auto const validator_id_storage = vars.validator_set.get(i);
        auto const validator_id = validator_id_storage.load();
        MONAD_ASSERT(validator_id.has_value());

        auto valinfo_storage = vars.validator_info(validator_id.value());
        auto valinfo = valinfo_storage.load();
        MONAD_ASSERT(valinfo.has_value());

        // TODO: apply commission rate
        valinfo->total_stake += valinfo->epoch_rewards;
        valinfo->active_stake += valinfo->epoch_rewards;
        valinfo->epoch_rewards = 0;
        valinfo_storage.store(valinfo.value());
    }

    // 2. Apply deposits
    StorageArray<uint256_t> deposit_queue_storage = vars.deposit_queue(epoch_);
    uint256_t const num_deposits = deposit_queue_storage.length();
    for (uint256_t i = 0; i < num_deposits; i += 1) {
        auto deposit_id = deposit_queue_storage.pop();
        auto deposit_request_storage = vars.deposit_request(deposit_id);
        auto deposit_request = deposit_request_storage.load();
        MONAD_ASSERT(deposit_request.has_value());

        auto valinfo_storage =
            vars.validator_info(deposit_request->validator_id);
        auto valinfo = valinfo_storage.load();
        MONAD_ASSERT(valinfo.has_value());

        auto delinfo_storage = vars.delegator_info(
            deposit_request->validator_id, deposit_request->delegator);
        auto delinfo = delinfo_storage.load();
        MONAD_ASSERT(delinfo.has_value());

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
    MONAD_ASSERT(deposit_queue_storage.length() == 0);

    // 3. Apply withdrawal requests
    StorageArray<uint256_t> withdrawal_queue_storage =
        vars.withdrawal_queue(epoch_);
    uint256_t const num_withdrawals = withdrawal_queue_storage.length();
    for (uint256_t i = 0; i < num_withdrawals; i += 1) {
        auto withdrawal_id = withdrawal_queue_storage.pop();
        auto withdrawal_request_storage =
            vars.withdrawal_request(withdrawal_id);
        auto withdrawal_request = withdrawal_request_storage.load();
        MONAD_ASSERT(withdrawal_request.has_value());

        auto valinfo_storage =
            vars.validator_info(withdrawal_request->validator_id);
        auto valinfo = valinfo_storage.load();
        MONAD_ASSERT(valinfo.has_value());

        auto delinfo_storage = vars.delegator_info(
            withdrawal_request->validator_id, withdrawal_request->delegator);
        auto delinfo = delinfo_storage.load();
        MONAD_ASSERT(delinfo.has_value());

        uint256_t const tokens_to_burn = shares_to_tokens(
            valinfo->active_stake,
            valinfo->active_shares,
            withdrawal_request->shares);

        valinfo->active_stake -= tokens_to_burn;
        valinfo->active_shares += withdrawal_request->shares;

        delinfo->active_shares -= withdrawal_request->shares;

        valinfo_storage.store(valinfo.value());
        delinfo_storage.store(delinfo.value());

        withdrawal_request_storage.clear();
    }
    MONAD_ASSERT(withdrawal_queue_storage.length() == 0);
}

MONAD_NAMESPACE_END
