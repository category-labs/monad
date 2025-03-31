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
    constexpr auto CONTRACT_ADDRESS =
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF_address; // fixme
    constexpr uint256_t MIN_STAKE_AMOUNT{1e18}; // 1 MON

    //////////////////////
    //      Crypto      //
    //////////////////////
    constexpr size_t SECP_COMPRESSED_PUBKEY_SIZE{33};
    constexpr size_t SECP_SIGNATURE_SIZE{64};

    constexpr size_t BLS_COMPRESSED_PUBKEY_SIZE{48};
    constexpr size_t BLS_COMPRESSED_SIGNATURE_SIZE{96};
}

//////////////////////////
//   Domain separators  //
//////////////////////////
namespace ds
{
    constexpr auto LAST_VALIDATOR_ID{
        0x41220a16053449faaa3a6d09af41bd3e_bytes32};
    constexpr auto LAST_STAKE_DELTA_ID{
        0x9e097777443c4f35945fb3a6db51d76c_bytes32};
    constexpr auto VALIDATOR_ID{0x92286cbe19ff43cfb4b0996357fd198b_bytes32};
    constexpr auto VALIDATOR_INFO{0xc4e9c9649cd24dbe8802efbb68ff43eb_bytes32};
    constexpr auto VALIDATOR_SET{0x5da123f52fc44a169234a9b18ac05821_bytes32};
    constexpr auto STAKE_DELTA{0x604c50570c7645f2a0663fe4c7a43133_bytes32};
    constexpr auto STAKE_DELTA_IDS{0x604c50570c7645f2a0663fe4c7a43133_bytes32};
    // constexpr auto
    // DELEGATOR_INFO{0xdce745101caa44dd9e41d4bc53a0300c_bytes32};
}

StakingContract::StakingContract(State &state, uint64_t const epoch)
    : state_{state}
    , epoch_{epoch}
    , last_validator_id_storage_{state, CONTRACT_ADDRESS, ds::LAST_VALIDATOR_ID}
    , last_stake_delta_id_storage_{state, CONTRACT_ADDRESS, ds::LAST_STAKE_DELTA_ID}
    , validator_set_storage_{state, CONTRACT_ADDRESS, ds::VALIDATOR_SET}

{
}

uint256_t StakingContract::next_validator_id() noexcept
{
    auto const id = last_validator_id_storage_.load().value_or(0);
    last_validator_id_storage_.store(id + 1);
    return id + 1;
}

uint256_t StakingContract::next_stake_delta_id() noexcept
{
    auto const id = last_stake_delta_id_storage_.load().value_or(0);
    last_stake_delta_id_storage_.store(id + 1);
    return id + 1;
}

std::optional<uint256_t>
StakingContract::get_validator_id(Address const &address) const noexcept
{
    StorageVariable<uint256_t> validator_id_storage{
        state_, CONTRACT_ADDRESS, mapping(ds::VALIDATOR_ID, address)};
    return validator_id_storage.load();
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

    auto const id = next_validator_id();

    Address const address = address_from_secpkey(secp_pubkey.serialize());
    StorageVariable<uint256_t> validator_id_storage{
        state_, CONTRACT_ADDRESS, mapping(ds::VALIDATOR_ID, address)};
    validator_id_storage.store(id);

    ValidatorInfo valinfo{
        .auth_address = unaligned_load<Address>(auth_address.data()),
        .bls_pubkey =
            unaligned_load<byte_string_fixed<48>>(bls_pubkey_serialized.data()),
        .total_stake = 0,
        .active_stake = 0,
        .activating_stake = 0,
        .deactivating_stake = 0,
        .epoch_rewards = 0};

    StorageVariable<ValidatorInfo> valinfo_storage(
        state_, CONTRACT_ADDRESS, mapping(ds::VALIDATOR_INFO, id));
    valinfo_storage.store(valinfo);
    validator_set_storage_.push(id);

    return EVMC_SUCCESS;
}

evmc_status_code StakingContract::add_stake(
    byte_string_view const input, evmc_message const &msg)
{
    // Validate input size
    if (MONAD_UNLIKELY(input.size() != SECP_COMPRESSED_PUBKEY_SIZE)) {
        return EVMC_REVERT;
    }
    thread_local std::unique_ptr<
        secp256k1_context,
        decltype(&secp256k1_context_destroy)> const
        context(
            secp256k1_context_create(SECP256K1_CONTEXT_VERIFY),
            &secp256k1_context_destroy);

    Secp256k1_Pubkey const secp_pubkey(*context.get(), input);
    if (MONAD_UNLIKELY(!secp_pubkey.is_valid())) {
        return EVMC_REVERT;
    }

    auto const amount = intx::be::load<uint256_t>(msg.value);
    if (MONAD_UNLIKELY(amount < MIN_STAKE_AMOUNT)) {
        return EVMC_REVERT;
    }

    Address const address = address_from_secpkey(secp_pubkey.serialize());
    auto const validator_id = get_validator_id(address);
    if (MONAD_UNLIKELY(!validator_id.has_value())) {
        return EVMC_REVERT;
    }

    auto const stake_delta_id = next_stake_delta_id();

    StorageArray<uint256_t> stake_delta_ids{
        state_, CONTRACT_ADDRESS, mapping(ds::STAKE_DELTA_IDS, epoch_)};
    stake_delta_ids.push(stake_delta_id);
    StorageVariable<StakeDelta> stake_delta{
        state_, CONTRACT_ADDRESS, mapping(ds::STAKE_DELTA, stake_delta_id)};
    stake_delta.store(StakeDelta{
        .validator_id = validator_id.value(),
        .amount = amount,
        .delegator = msg.sender,
        .is_deposit = true});

    return EVMC_SUCCESS;
}

#if 0
evmc_status_code StakingContract::remove_stake(
    byte_string_view const input, evmc_message const &msg)
{
    uint256_t const validator_id = ;
    StorageVariable<DelegatorInfo> delegator(
        state_,
        CONTRACT_ADDRESS,
        mapping(ds::DELEGATOR_INFO, validator_id, msg.sender));
}
#endif

MONAD_NAMESPACE_END
