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

#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/monad/staking/test/input_generation.hpp>
#include <category/execution/monad/staking/util/secp256k1.hpp>

#include <category/core/blake3.hpp>

#include <memory>

namespace
{
    std::unique_ptr<secp256k1_context, decltype(&secp256k1_context_destroy)>
        secp_context(
            secp256k1_context_create(
                SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY),
            secp256k1_context_destroy);
}

namespace monad::staking::test
{
    std::pair<blst_p1, blst_scalar> gen_bls_keypair(bytes32_t secret)
    {
        blst_scalar secret_key;
        blst_p1 public_key;

        blst_keygen(&secret_key, secret.bytes, sizeof(secret));
        blst_sk_to_pk_in_g1(&public_key, &secret_key);
        return {public_key, secret_key};
    }

    std::pair<secp256k1_pubkey, bytes32_t> gen_secp_keypair(bytes32_t secret)
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
                     NULL));

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

    std::tuple<byte_string, byte_string, byte_string, Address>
    craft_add_validator_input_raw(
        Address const &auth_address, uint256_t const &stake,
        uint256_t const &commission, bytes32_t secret)
    {
        auto const [bls_pubkey, bls_seckey] = gen_bls_keypair(secret);
        auto const [secp_pubkey, secp_seckey] = gen_secp_keypair(secret);

        auto const secp_pubkey_serialized = serialize_secp_pubkey(secp_pubkey);
        auto const bls_pubkey_serialized = [&bls_pubkey] {
            byte_string_fixed<48> serialized;
            blst_p1_compress(serialized.data(), &bls_pubkey);
            return serialized;
        }();

        auto const sign_address = address_from_secpkey(
            serialize_secp_pubkey_uncompressed(secp_pubkey));

        byte_string message;
        message += to_byte_string_view(secp_pubkey_serialized);
        message += to_byte_string_view(bls_pubkey_serialized);
        message += to_byte_string_view(auth_address.bytes);
        message += to_byte_string_view(intx::be::store<bytes32_t>(stake).bytes);
        message += to_byte_string_view(u256_be{commission}.bytes);

        // sign with both keys
        byte_string const secp_sig{
            to_byte_string_view(sign_secp(message, secp_seckey))};
        byte_string const bls_sig{
            to_byte_string_view(sign_bls(message, bls_seckey))};

        return {message, secp_sig, bls_sig, sign_address};
    }

    std::pair<byte_string, Address> craft_add_validator_input(
        Address const &auth_address, uint256_t const &stake,
        uint256_t const &commission, bytes32_t secret)
    {
        auto const [message, secp_sig, bls_sig, sign_address] =
            craft_add_validator_input_raw(
                auth_address, stake, commission, secret);
        AbiEncoder encoder;
        encoder.add_bytes(message);
        encoder.add_bytes(secp_sig);
        encoder.add_bytes(bls_sig);
        return {encoder.encode_final(), sign_address};
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
