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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/monad/staking/test/input_generation.hpp>
#include <category/execution/monad/staking/util/secp256k1.hpp>

#include <category/core/blake3.hpp>

#include <blst.h>
#include <secp256k1.h>

#include <algorithm>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <tuple>
#include <utility>

namespace
{
    std::unique_ptr<secp256k1_context, void (*)(secp256k1_context *)>
        secp_context(
            secp256k1_context_create(
                SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY),
            secp256k1_context_destroy);
}

namespace monad::staking::test
{
    std::pair<blst_p1, blst_scalar> gen_bls_keypair(bytes32_t const secret)
    {
        blst_scalar secret_key;
        blst_p1 public_key;

        blst_keygen(&secret_key, secret.bytes, sizeof(secret));
        blst_sk_to_pk_in_g1(&public_key, &secret_key);
        return {public_key, secret_key};
    }

    std::pair<secp256k1_pubkey, bytes32_t>
    gen_secp_keypair(bytes32_t const secret)
    {
        secp256k1_pubkey public_key;

        MONAD_ASSERT(
            1 == secp256k1_ec_pubkey_create(
                     secp_context.get(), &public_key, secret.bytes));

        return {public_key, secret};
    }

    byte_string_fixed<33> serialize_secp_pubkey(secp256k1_pubkey const &pubkey)
    {
        byte_string_fixed<33> secp_pubkey_serialized;
        size_t size = 33;
        MONAD_ASSERT(
            1 == secp256k1_ec_pubkey_serialize(
                     secp_context.get(),
                     secp_pubkey_serialized.data(),
                     &size,
                     &pubkey,
                     SECP256K1_EC_COMPRESSED));
        MONAD_ASSERT(size == 33);
        return secp_pubkey_serialized;
    }

    byte_string_fixed<64>
    sign_secp(byte_string_view const message, bytes32_t const &seckey)
    {
        secp256k1_ecdsa_signature sig;
        auto const digest = blake3(message);
        MONAD_ASSERT(
            1 == secp256k1_ecdsa_sign(
                     secp_context.get(),
                     &sig,
                     digest.bytes,
                     seckey.bytes,
                     secp256k1_nonce_function_default,
                     nullptr));

        byte_string_fixed<64> serialized;
        MONAD_ASSERT(
            1 == secp256k1_ecdsa_signature_serialize_compact(
                     secp_context.get(), serialized.data(), &sig));
        return serialized;
    }

    byte_string_fixed<96>
    sign_bls(byte_string_view const message, blst_scalar const &seckey)
    {
        static constexpr char DST[] =
            "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_";
        blst_p2 hash;
        blst_hash_to_g2(
            &hash,
            message.data(),
            message.size(),
            reinterpret_cast<uint8_t const *>(DST),
            sizeof(DST) - 1,
            nullptr,
            0);
        blst_p2 sig;
        blst_sign_pk_in_g1(&sig, &hash, &seckey);

        byte_string_fixed<96> serialized;
        blst_p2_compress(serialized.data(), &sig);
        return serialized;
    }

    byte_string_fixed<65>
    serialize_secp_pubkey_uncompressed(secp256k1_pubkey const &pubkey)
    {
        byte_string_fixed<65> secp_pubkey_serialized;
        size_t size = 65;
        MONAD_ASSERT(
            1 == secp256k1_ec_pubkey_serialize(
                     secp_context.get(),
                     secp_pubkey_serialized.data(),
                     &size,
                     &pubkey,
                     SECP256K1_EC_UNCOMPRESSED));
        MONAD_ASSERT(size == 65);
        return secp_pubkey_serialized;
    }

    ReceiverKeyProof prove_receiver_key_registration(
        uint256_be_t const &chain_id, Address const &validator_address,
        byte_string_fixed<48> const &bls_pubkey, Address const &auth_address,
        bytes32_t const &secret, std::optional<bytes32_t> nonce_override)
    {
        auto const public_key =
            serialize_secp_pubkey(gen_secp_keypair(secret).first);
        auto const base = receiver_key_registration_base(
            chain_id, validator_address, bls_pubkey, auth_address, public_key);
        MONAD_ASSERT(base.has_value());
        // Test-only deterministic nonce; production proof generation uses fresh
        // randomness. This fixture binds its nonce to the registration inputs.
        byte_string nonce_input{
            to_byte_string_view("staking-test/receiver-key-proof/v1")};
        nonce_input += to_byte_string_view(secret.bytes);
        nonce_input += to_byte_string_view(chain_id.bytes);
        nonce_input += to_byte_string_view(validator_address.bytes);
        nonce_input += to_byte_string_view(bls_pubkey);
        nonce_input += to_byte_string_view(auth_address.bytes);
        auto const nonce =
            nonce_override.value_or(to_bytes(blake3(nonce_input)));
        auto image = *base;
        auto v0 = *base;
        MONAD_ASSERT(
            secp256k1_ec_pubkey_tweak_mul(
                secp_context.get(), &image, secret.bytes) == 1);
        MONAD_ASSERT(
            secp256k1_ec_pubkey_tweak_mul(
                secp_context.get(), &v0, nonce.bytes) == 1);
        auto const u0 = gen_secp_keypair(nonce).first;
        auto const encoded_image = serialize_secp_pubkey(image);
        auto const challenge = receiver_key_registration_challenge(
            *base, public_key, encoded_image, u0, v0);
        auto z = secret;
        if (challenge == bytes32_t{}) {
            z = nonce;
        }
        else {
            MONAD_ASSERT(
                secp256k1_ec_seckey_tweak_mul(
                    secp_context.get(), z.bytes, challenge.bytes) == 1);
            if (secp256k1_ec_seckey_tweak_add(
                    secp_context.get(), z.bytes, nonce.bytes) != 1) {
                z = bytes32_t{};
            }
        }
        return ReceiverKeyProof{
            .image = encoded_image, .challenge = challenge, .response = z};
    }

    static byte_string encode_receiver_key_proof(ReceiverKeyProof const &proof)
    {
        AbiEncoder encoder;
        encoder.add_bytes(to_byte_string_view(proof.image));
        encoder.add_uint(std::bit_cast<u256_be>(proof.challenge));
        encoder.add_uint(std::bit_cast<u256_be>(proof.response));
        return encoder.encode_final();
    }

    byte_string ValidatorRegistration::encode() const
    {
        AbiEncoder encoder;
        encoder.add_bytes(message);
        encoder.add_bytes(to_byte_string_view(secp_signature));
        encoder.add_bytes(to_byte_string_view(bls_signature));
        if (receiver_proof) {
            encoder.add_tuple(encode_receiver_key_proof(*receiver_proof));
        }
        return encoder.encode_final();
    }

    byte_string craft_add_receiver_key_input(
        u64_be const id, byte_string_fixed<33> const &key,
        ReceiverKeyProof const &proof)
    {
        AbiEncoder encoder;
        encoder.add_uint(id);
        encoder.add_bytes(to_byte_string_view(key));
        encoder.add_tuple(encode_receiver_key_proof(proof));
        return encoder.encode_final();
    }

    ValidatorRegistration make_validator_registration(
        Address const &auth_address, uint256_t const &stake,
        uint256_t const &commission, bytes32_t const secret,
        bool const receiver_enabled, std::optional<bytes32_t> receiver_override)
    {
        auto const [bls_pubkey, bls_seckey] = gen_bls_keypair(secret);
        auto const [secp_pubkey, secp_seckey] = gen_secp_keypair(secret);

        auto const secp_pubkey_serialized = serialize_secp_pubkey(secp_pubkey);
        auto const bls_pubkey_serialized = [](blst_p1 const &pubkey) {
            byte_string_fixed<48> serialized;
            blst_p1_compress(serialized.data(), &pubkey);
            return serialized;
        }(bls_pubkey);

        auto const sign_address = address_from_secpkey(
            serialize_secp_pubkey_uncompressed(secp_pubkey));

        byte_string message;
        message += to_byte_string_view(secp_pubkey_serialized);
        message += to_byte_string_view(bls_pubkey_serialized);
        std::optional<ReceiverKeyProof> receiver_proof;
        if (receiver_enabled) {
            auto const receiver_secret = receiver_override.value_or(
                to_bytes(blake3(to_byte_string_view(secret.bytes))));
            message += to_byte_string_view(
                serialize_secp_pubkey(gen_secp_keypair(receiver_secret).first));
            receiver_proof = prove_receiver_key_registration(
                {},
                sign_address,
                bls_pubkey_serialized,
                auth_address,
                receiver_secret);
        }
        message += to_byte_string_view(auth_address.bytes);
        message += to_byte_string_view(store_be_as<bytes32_t>(stake).bytes);
        message += to_byte_string_view(u256_be{commission}.bytes);

        auto const secp_signature = sign_secp(message, secp_seckey);
        auto const bls_signature = sign_bls(message, bls_seckey);
        return {
            std::move(message),
            secp_signature,
            bls_signature,
            receiver_proof,
            auth_address,
            sign_address};
    }

    std::pair<byte_string, Address> craft_add_validator_input(
        Address const &auth_address, uint256_t const &stake,
        uint256_t const &commission, bytes32_t const secret,
        bool const receiver_enabled)
    {
        auto const val = make_validator_registration(
            auth_address, stake, commission, secret, receiver_enabled);
        return {val.encode(), val.sign_address};
    }

    byte_string craft_undelegate_input(
        u64_be const val_id, uint256_t const &amount, u8_be const withdrawal_id)
    {
        AbiEncoder encoder;
        encoder.add_uint(val_id);
        encoder.add_uint<u256_be>(amount);
        encoder.add_uint(withdrawal_id);
        return encoder.encode_final();
    }

    byte_string
    craft_withdraw_input(u64_be const val_id, u8_be const withdrawal_id)
    {
        AbiEncoder encoder;
        encoder.add_uint(val_id);
        encoder.add_uint(withdrawal_id);
        return encoder.encode_final();
    }

    byte_string craft_change_commission_input(
        u64_be const val_id, uint256_t const &commission)
    {
        AbiEncoder encoder;
        encoder.add_uint(val_id);
        encoder.add_uint<u256_be>(commission);
        return encoder.encode_final();
    }
}
