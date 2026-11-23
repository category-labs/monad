// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/assert.h>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/domain/ale/application_encryption_contract.hpp>
#include <category/execution/domain/ale/application_encryption_error.hpp>
#include <category/execution/ethereum/core/contract/abi_decode.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <boost/outcome/try.hpp>

#include <algorithm>
#include <limits>
#include <string_view>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

constexpr std::string_view SEALED_BLOB_AD_LABEL = "monad-sealed-blob-v1";
constexpr std::string_view SEALED_BLOB_RANDOMNESS_LABEL =
    "monad-precompile-randomness-v1";

struct PrecompileSelector
{
    static constexpr uint32_t SEAL_MESSAGE =
        abi_encode_selector("sealMessage(uint64,uint256,bytes)");
    static constexpr uint32_t SEAL_BLOB =
        abi_encode_selector("seal(bytes,uint64,address,bytes)");
    static constexpr uint32_t UNSEAL_BLOB =
        abi_encode_selector("unseal(bytes,bytes)");
};

static_assert(PrecompileSelector::SEAL_MESSAGE == 0x5760b04f);
static_assert(PrecompileSelector::SEAL_BLOB == 0x607c42c9);
static_assert(PrecompileSelector::UNSEAL_BLOB == 0x8f5b97f5);

// TODO: Specify the actual costs, including input-length pricing for
// message and blob encryption, before registering.
constexpr uint64_t SEAL_MESSAGE_OP_COST = 100;
constexpr uint64_t SEAL_BLOB_OP_COST = 100;
constexpr uint64_t UNSEAL_BLOB_OP_COST = 100;
constexpr uint64_t FALLBACK_COST = 100;

uint64_t seal_message_gas_cost(byte_string_view const)
{
    return SEAL_MESSAGE_OP_COST;
}

uint64_t seal_blob_gas_cost(byte_string_view const)
{
    return SEAL_BLOB_OP_COST;
}

uint64_t unseal_blob_gas_cost(byte_string_view const)
{
    return UNSEAL_BLOB_OP_COST;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

byte_string sealed_blob_ad(
    uint64_t const dest_domain, Address const &to,
    byte_string_view const app_ctx)
{
    AbiEncoder encoder;
    encoder.add_string(SEALED_BLOB_AD_LABEL);
    encoder.add_uint(u64_be{dest_domain});
    encoder.add_address(to);
    encoder.add_bytes(app_ctx);
    return encoder.encode_final();
}

byte_string sealed_blob_randomness_input(
    Address const &tx_origin, uint64_t const tx_nonce,
    uint64_t const seal_index, Address const &caller,
    bytes32_t const &destination_key, byte_string_view const ad,
    byte_string_view const blob)
{
    AbiEncoder encoder;
    encoder.add_string(SEALED_BLOB_RANDOMNESS_LABEL);
    encoder.add_address(tx_origin);
    encoder.add_uint(u64_be{tx_nonce});
    encoder.add_uint(u64_be{seal_index});
    encoder.add_address(caller);
    encoder.add_bytes({destination_key.bytes, sizeof(destination_key.bytes)});
    encoder.add_bytes(ad);
    encoder.add_bytes(blob);
    return encoder.encode_final();
}

Result<bytes32_t> read_destination_key(
    State &state, Address const &spoke, uint256_t const &mapping_slot,
    uint64_t destination_domain)
{
    if (!state.account_exists(spoke)) {
        return ApplicationEncryptionError::SpokeNotFound;
    }

    AbiEncoder encoder;
    encoder.add_uint(u64_be{destination_domain});
    encoder.add_uint(u256_be{mapping_slot});
    auto const storage_key = to_bytes(keccak256(encoder.encode_final()));
    auto const public_key = state.get_storage(spoke, storage_key);

    if (public_key == bytes32_t{}) {
        return ApplicationEncryptionError::DestinationKeyNotFound;
    }

    return public_key;
}

ApplicationEncryptionContract::ApplicationEncryptionContract(
    State &state, CallTracerBase &tracer,
    ApplicationEncryptionContext const &encryption_context,
    Address const &tx_origin, uint64_t const tx_nonce,
    bool const log_native_transfers)
    : state_{state}
    , call_tracer_{tracer}
    , log_native_transfers_{log_native_transfers}
    , encryption_context_{encryption_context}
    , tx_origin_{tx_origin}
    , tx_nonce_{tx_nonce}
{
}

template <Traits traits>
std::pair<ApplicationEncryptionContract::PrecompileFunc, uint64_t>
ApplicationEncryptionContract::precompile_dispatch(byte_string_view &input)
{
    if (input.size() < 4) {
        return {
            &ApplicationEncryptionContract::precompile_fallback, FALLBACK_COST};
    }

    auto const selector = load_be_unsafe<uint32_t>(input.data());
    input.remove_prefix(4);

    switch (selector) {
    // The handler receives input with the four-byte selector removed.
    case PrecompileSelector::SEAL_MESSAGE:
        return {
            &ApplicationEncryptionContract::precompile_seal_message,
            seal_message_gas_cost(input)};
    case PrecompileSelector::SEAL_BLOB:
        return {
            &ApplicationEncryptionContract::precompile_seal,
            seal_blob_gas_cost(input)};
    case PrecompileSelector::UNSEAL_BLOB:
        return {
            &ApplicationEncryptionContract::precompile_unseal,
            unseal_blob_gas_cost(input)};
    default:
        return {
            &ApplicationEncryptionContract::precompile_fallback, FALLBACK_COST};
    }
}

EXPLICIT_MONAD_TRAITS(ApplicationEncryptionContract::precompile_dispatch);

Result<byte_string> ApplicationEncryptionContract::precompile_seal_message(
    byte_string_view input, Address const &, uint256_be_t const &msg_value)
{
    if (std::ranges::any_of(
            msg_value.bytes, [](uint8_t const byte) { return byte != 0; })) {
        return ApplicationEncryptionError::ValueNonZero;
    }

    BOOST_OUTCOME_TRY(
        auto const destination_domain, abi_decode_fixed<u64_be>(input));
    BOOST_OUTCOME_TRY(
        [[maybe_unused]] auto const sequence_number,
        abi_decode_fixed<u256_be>(input));

    // Skip the plaintext offset and read its tail after the three-word head.
    BOOST_OUTCOME_TRY(abi_decode_fixed<u256_be>(input));
    BOOST_OUTCOME_TRY(
        [[maybe_unused]] byte_string_view plaintext,
        abi_decode_dynamic_bytes_tail(input));

    BOOST_OUTCOME_TRY(
        [[maybe_unused]] auto const key,
        read_destination_key(
            state_,
            encryption_context_.spoke,
            SPOKE_VIEWING_KEYS_SLOT,
            destination_domain.native()));

    // TODO: Encode AD with encryption_context_.domain_chain_id as source:
    // abi.encode("monad-cross-domain-encryption-v1", source_domain,
    // destination_domain, sequence_number), preserving the uint256 nonce.
    // TODO: Derive randomness from the domain seed, sequence number, caller,
    // transaction context, destination key, AD and plaintext.
    // TODO: HPKE Seal the opaque plaintext and ABI-encode the ciphertext as
    // bytes for IDomainEncryption. The spoke encodes (from, to, data).
    return ApplicationEncryptionError::NotImplemented;
}

uint64_t ApplicationEncryptionContract::next_seal_index()
{
    // Transient storage shares the index within one transaction and rolls
    // increments back when the calling frame reverts.
    auto const index = load_be<uint256_t>(
        state_.get_transient_storage(ALE_CA, SEAL_INDEX_SLOT));
    MONAD_ASSERT(index < uint256_t{std::numeric_limits<uint64_t>::max()});
    auto const seal_index = static_cast<uint64_t>(index);
    state_.set_transient_storage(
        ALE_CA, SEAL_INDEX_SLOT, bytes32_t{seal_index + 1});
    return seal_index;
}

Result<byte_string> ApplicationEncryptionContract::precompile_seal(
    byte_string_view input, Address const &msg_sender,
    uint256_be_t const &msg_value)
{
    if (std::ranges::any_of(
            msg_value.bytes, [](uint8_t const byte) { return byte != 0; })) {
        return ApplicationEncryptionError::ValueNonZero;
    }

    // Skip blob offset: sequential read will obtain the length dynamically
    BOOST_OUTCOME_TRY(abi_decode_fixed<u256_be>(input));

    BOOST_OUTCOME_TRY(auto const dest_domain, abi_decode_fixed<u64_be>(input));
    BOOST_OUTCOME_TRY(auto const to_addr, abi_decode_fixed<Address>(input));

    // Likewise skip app ctx offset
    BOOST_OUTCOME_TRY(abi_decode_fixed<u256_be>(input));

    BOOST_OUTCOME_TRY(
        byte_string_view blob, abi_decode_dynamic_bytes_tail(input));
    BOOST_OUTCOME_TRY(
        byte_string_view app_ctx, abi_decode_dynamic_bytes_tail(input));

    // Associated data binds the sealed blob to an intended recipient
    // context.
    auto const ad = sealed_blob_ad(dest_domain.native(), to_addr, app_ctx);

    BOOST_OUTCOME_TRY(
        auto const key,
        read_destination_key(
            state_,
            encryption_context_.spoke,
            SPOKE_VIEWING_KEYS_SLOT,
            dest_domain.native()));
    auto const seal_index = next_seal_index();
    [[maybe_unused]] auto const randomness_input = sealed_blob_randomness_input(
        tx_origin_, tx_nonce_, seal_index, msg_sender, key, ad, blob);

    // TODO: Pass blob, key, ad and randomness_input to
    // encryption_context_.key.seal() and ABI-encode the ciphertext.
    return ApplicationEncryptionError::NotImplemented;
}

Result<byte_string> ApplicationEncryptionContract::precompile_unseal(
    byte_string_view input, Address const &msg_sender,
    uint256_be_t const &msg_value)
{
    if (std::ranges::any_of(
            msg_value.bytes, [](uint8_t const byte) { return byte != 0; })) {
        return ApplicationEncryptionError::ValueNonZero;
    }

    // Skip the offsets and read the two tails in argument order.
    BOOST_OUTCOME_TRY(abi_decode_fixed<u256_be>(input));
    BOOST_OUTCOME_TRY(abi_decode_fixed<u256_be>(input));

    BOOST_OUTCOME_TRY(
        [[maybe_unused]] byte_string_view sealed_blob,
        abi_decode_dynamic_bytes_tail(input));
    BOOST_OUTCOME_TRY(
        byte_string_view app_ctx, abi_decode_dynamic_bytes_tail(input));

    // Unseal (sealed_blob, app_ctx) for msg_sender on the executing domain.
    // TODO: Specify the length-based gas schedule. Input excludes the selector.

    [[maybe_unused]] auto const ad = sealed_blob_ad(
        encryption_context_.domain_chain_id, msg_sender, app_ctx);
    // TODO: Open with encryption_context_.key and ad, then encode the
    // plaintext. Do not increment the Seal index.
    // TODO: Enforce empty revert data for every unseal failure and the
    // specified length-based gas charge in the wrapper before registration.
    return ApplicationEncryptionError::NotImplemented;
}

Result<byte_string> ApplicationEncryptionContract::precompile_fallback(
    byte_string_view, Address const &, uint256_be_t const &)
{
    return ApplicationEncryptionError::MethodNotSupported;
}

MONAD_NAMESPACE_END
