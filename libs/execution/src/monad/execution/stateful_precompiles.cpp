#include <monad/core/int.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/likely.h>
#include <monad/core/unaligned.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/staking/bls.hpp>
#include <monad/execution/staking/secp256k1.hpp>
#include <monad/execution/staking/storage.hpp>
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
    constexpr auto METADATA_STORAGE_SLOT = bytes32_t{};
    constexpr uint256_t MIN_STAKE_AMOUNT{1e18}; // 1 MON

    uint64_t const MAX_DEPOSIT_REQUESTS_PER_EPOCH = 100;
    uint64_t const MAX_WITHDRAWAL_REQUESTS_PER_EPOCH = 100;

    //////////////////////
    //      Crypto      //
    //////////////////////
    constexpr size_t SECP_COMPRESSED_PUBKEY_SIZE{33};
    constexpr size_t SECP_SIGNATURE_SIZE{64};

    constexpr size_t BLS_COMPRESSED_PUBKEY_SIZE{48};
    constexpr size_t BLS_COMPRESSED_SIGNATURE_SIZE{96};
}

StatefulPrecompile::StatefulPrecompile(State &state, uint64_t const epoch)
    : state_{state}
    , epoch_{epoch}

{
}

evmc_status_code StatefulPrecompile::stake_deposit(
    byte_string_view const input, evmc_message const &msg)
{
    constexpr size_t DEPOSIT_MESSAGE_SIZE = SECP_COMPRESSED_PUBKEY_SIZE +
                                            BLS_COMPRESSED_PUBKEY_SIZE +
                                            sizeof(Address);
    constexpr size_t SIGNATURES_SIZE =
        SECP_SIGNATURE_SIZE + BLS_COMPRESSED_SIGNATURE_SIZE;

    constexpr size_t EXPECTED_INPUT_SIZE =
        DEPOSIT_MESSAGE_SIZE + SIGNATURES_SIZE;

    // Validate input size
    if (MONAD_UNLIKELY(input.size() != EXPECTED_INPUT_SIZE)) {
        return EVMC_REVERT;
    }

    uint256_t const amount_to_stake = intx::be::load<uint256_t>(msg.value);

    // extract individual inputs
    byte_string_view message = input.substr(0, DEPOSIT_MESSAGE_SIZE);

    byte_string_view reader = input;
    byte_string_view secp_pubkey_serialized =
        read_bytes(reader, SECP_COMPRESSED_PUBKEY_SIZE);
    byte_string_view bls_pubkey_serialized =
        read_bytes(reader, BLS_COMPRESSED_PUBKEY_SIZE);
    byte_string_view withdrawal_address = read_bytes(reader, sizeof(Address));
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

    // Check if stake amount meets minimum requirement
    if (MONAD_UNLIKELY(amount_to_stake < MIN_STAKE_AMOUNT)) {
        return EVMC_REVERT;
    }

    bytes32_t raw_metadata =
        state_.get_storage(CONTRACT_ADDRESS, METADATA_STORAGE_SLOT);
    auto *metadata = reinterpret_cast<StakeMetadata *>(raw_metadata.bytes + 12);
    if (metadata->deposit_queue_size == MAX_WITHDRAWAL_REQUESTS_PER_EPOCH) {
        return EVMC_REVERT;
    }
    metadata->deposit_queue_size += 1;
    state_.set_storage(CONTRACT_ADDRESS, METADATA_STORAGE_SLOT, raw_metadata);

    Address address = address_from_secpkey(secp_pubkey.serialize());
    ValidatorStorageKeyGenerator gen(address);
    StorageAdapter<ValidatorInfo> storage;
    for (uint8_t i = 0; i < static_cast<uint8_t>(storage.slots.size()); ++i) {
        storage.slots[i] = state_.get_storage(CONTRACT_ADDRESS, gen.key(i));
    }

    ValidatorInfo &info = storage.typed;
    bool const is_new_validator = std::all_of(
        info.bls_pubkey.data(),
        info.bls_pubkey.data() + info.bls_pubkey.size(),
        [](uint8_t const byte) { return byte == 0x00; });
    if (!is_new_validator) {
        // validator exists in set
        return EVMC_REVERT;
    }

    info.stake = amount_to_stake;
    info.join_epoch = epoch_;
    info.bls_pubkey =
        unaligned_load<byte_string_fixed<48>>(bls_pubkey_serialized.data());
    info.withdrawal_address =
        unaligned_load<Address>(withdrawal_address.data());

    for (uint8_t i = 0; i < static_cast<uint8_t>(storage.slots.size()); ++i) {
        state_.set_storage(CONTRACT_ADDRESS, gen.key(i), storage.slots[i]);
    }
    return EVMC_SUCCESS;
}

evmc_status_code
StatefulPrecompile::stake_withdraw(byte_string_view const, evmc_message const &)
{
    // TODO
    return EVMC_REVERT;
}

MONAD_NAMESPACE_END
