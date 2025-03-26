#include <monad/contract/mapping.hpp>
#include <monad/contract/storage_variable.hpp>
#include <monad/core/blake3.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/unaligned.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/staking/bls.hpp>
#include <monad/execution/staking/secp256k1.hpp>
#include <monad/execution/staking/validator.hpp>
#include <monad/execution/stateful_precompiles.hpp>
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
    // constexpr uint256_t MIN_STAKE_AMOUNT{1e18}; // 1 MON

    //////////////////////
    //      Crypto      //
    //////////////////////
    constexpr size_t SECP_COMPRESSED_PUBKEY_SIZE{33};
    constexpr size_t SECP_SIGNATURE_SIZE{64};

    constexpr size_t BLS_COMPRESSED_PUBKEY_SIZE{48};
    constexpr size_t BLS_COMPRESSED_SIGNATURE_SIZE{96};

    //////////////////////
    // Domain separator //
    //////////////////////
    constexpr auto LAST_VALIDATOR_ID_DS{
        0x41220a16053449faaa3a6d09af41bd3e_bytes32};
    constexpr auto VALIDATOR_ID_DS{0x92286cbe19ff43cfb4b0996357fd198b_bytes32};
    constexpr auto VALIDATOR_INFO_DS{
        0xc4e9c9649cd24dbe8802efbb68ff43eb_bytes32};
}

StatefulPrecompile::StatefulPrecompile(State &state, uint64_t const epoch)
    : state_{state}
    , epoch_{epoch}

{
}

evmc_status_code StatefulPrecompile::create_validator(
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

    StorageVariable<uint256_t> last_validator_id_storage(
        state_, CONTRACT_ADDRESS, LAST_VALIDATOR_ID_DS);
    auto validator_id = last_validator_id_storage.load();
    validator_id += 1;
    last_validator_id_storage.store(validator_id);

    // create mapping(address => uint256) validator_id
    Address address = address_from_secpkey(secp_pubkey.serialize());
    auto const validator_id_key = mapping(VALIDATOR_ID_DS, address);

    // auto const validator_id_key =
    //     to_bytes(blake3(to_byte_string_view(VALIDATOR_ID_MAPPING.bytes)));
    // StorageAdapter<Address> mapping(address);
    StorageVariable<uint256_t> validator_id_storage(
        state_, CONTRACT_ADDRESS, validator_id_key);
    validator_id_storage.store(validator_id);

    ValidatorInfo validator_info;
    StorageVariable<ValidatorInfo> validator_info_storage(
        state_, CONTRACT_ADDRESS, mapping(VALIDATOR_INFO_DS, validator_id));
    validator_info_storage.store(ValidatorInfo{
        .auth_address = unaligned_load<Address>(auth_address.data()),
        .bls_pubkey =
            unaligned_load<byte_string_fixed<48>>(bls_pubkey_serialized.data()),
        .stake = 0,
        .active_stake = 0,
        .join_epoch = epoch_});

    return EVMC_SUCCESS;
}

evmc_status_code
StatefulPrecompile::stake_withdraw(byte_string_view const, evmc_message const &)
{
    // TODO
    return EVMC_REVERT;
}

MONAD_NAMESPACE_END
