// Copyright (C) 2026 Category Labs, Inc.
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

#include <category/execution/monad/staking/util/receiver_key.hpp>

#include <category/core/int.hpp>
#include <category/execution/ethereum/core/contract/abi_decode.hpp>
#include <category/execution/monad/staking/util/rfc9380_secp256k1.hpp>

#include <algorithm>
#include <bit>

MONAD_STAKING_ANONYMOUS_NAMESPACE_BEGIN

// Domain separation for the receiver-key registration base and challenge.
constexpr auto BASE_DST = "\x13"
                          "btx-dkg/pop-base/1\n";
constexpr auto CHALLENGE_DST = "\x13"
                               "btx-dkg/pop-chal/1\n";

byte_string_fixed<33> compressed(secp256k1_pubkey const &point)
{
    byte_string_fixed<33> bytes;
    size_t size = bytes.size();
    auto const result = secp256k1_ec_pubkey_serialize(
        get_secp_context(),
        bytes.data(),
        &size,
        &point,
        SECP256K1_EC_COMPRESSED);
    MONAD_ASSERT(result == 1 && size == bytes.size());
    return bytes;
}

bool canonical_scalar(bytes32_t const &scalar)
{
    return load_be<uint256_t>(scalar) < SECP256K1_SCALAR_ORDER;
}

// BTX DKG specification, Section 2.1, BVE.PoPVerify step 3:
// compute z*base - challenge*public, with (-challenge) mod n supplied by the
// caller. The zero cases are explicit because
// libsecp256k1 public keys cannot represent the point at infinity. An identity
// result has no compressed encoding in the proof transcript, so it is rejected.
std::optional<secp256k1_pubkey> reconstruct(
    secp256k1_pubkey const &base, secp256k1_pubkey const &public_key,
    bytes32_t const &z, bytes32_t const &negated_challenge)
{
    auto const *context = get_secp_context();
    bool const z_nonzero = z != bytes32_t{};
    bool const challenge_nonzero = negated_challenge != bytes32_t{};
    if (!z_nonzero && !challenge_nonzero) {
        return std::nullopt;
    }
    secp256k1_pubkey first = base;
    secp256k1_pubkey second = public_key;
    if (z_nonzero &&
        secp256k1_ec_pubkey_tweak_mul(context, &first, z.bytes) != 1) {
        return std::nullopt;
    }
    if (challenge_nonzero) {
        if (secp256k1_ec_pubkey_tweak_mul(
                context, &second, negated_challenge.bytes) != 1) {
            return std::nullopt;
        }
    }
    if (!z_nonzero) {
        return second;
    }
    if (!challenge_nonzero) {
        return first;
    }
    secp256k1_pubkey const *terms[] = {&first, &second};
    secp256k1_pubkey sum;
    if (secp256k1_ec_pubkey_combine(context, &sum, terms, 2) != 1) {
        return std::nullopt;
    }
    return sum;
}

MONAD_STAKING_ANONYMOUS_NAMESPACE_END

MONAD_STAKING_NAMESPACE_BEGIN

Result<ReceiverKeyProof> decode_receiver_key_proof(byte_string_view &input)
{
    BOOST_OUTCOME_TRY(abi_decode_fixed<u256_be>(input)); // image tail offset
    BOOST_OUTCOME_TRY(auto const challenge, abi_decode_fixed<u256_be>(input));
    BOOST_OUTCOME_TRY(auto const response, abi_decode_fixed<u256_be>(input));
    BOOST_OUTCOME_TRY(auto const image, abi_decode_bytes_tail<33>(input));
    return ReceiverKeyProof{
        .image = image,
        .challenge = std::bit_cast<bytes32_t>(challenge),
        .response = std::bit_cast<bytes32_t>(response)};
}

std::optional<secp256k1_pubkey> receiver_key_registration_base(
    uint256_be_t const &chain_id, Address const &validator_address,
    byte_string_fixed<48> const &bls_pubkey, Address const &auth_address,
    byte_string_fixed<33> const &public_key)
{
    byte_string_fixed<32 + 20 + 48 + 20 + 33> message;
    auto out =
        std::copy_n(chain_id.bytes, sizeof(chain_id.bytes), message.begin());
    out = std::copy_n(
        validator_address.bytes, sizeof(validator_address.bytes), out);
    out = std::copy(bls_pubkey.begin(), bls_pubkey.end(), out);
    out = std::copy_n(auth_address.bytes, sizeof(auth_address.bytes), out);
    std::copy(public_key.begin(), public_key.end(), out);
    return hash_to_secp256k1(
        to_byte_string_view(message), to_byte_string_view(BASE_DST));
}

bytes32_t receiver_key_registration_challenge(
    secp256k1_pubkey const &base, byte_string_fixed<33> const &public_key,
    byte_string_fixed<33> const &image, secp256k1_pubkey const &a,
    secp256k1_pubkey const &b)
{
    // Each compressed point is
    // a fixed 33-byte input, concatenated in the order Hchall(Q, pk, I, A, B).
    byte_string_fixed<5 * 33> message;
    auto out = message.begin();
    for (auto const &point :
         {compressed(base), public_key, image, compressed(a), compressed(b)}) {
        out = std::copy(point.begin(), point.end(), out);
    }
    auto const challenge = hash_to_secp256k1_scalar(
        to_byte_string_view(message), to_byte_string_view(CHALLENGE_DST));
    MONAD_ASSERT(challenge.has_value()); // The fixed DST is valid.
    return *challenge;
}

std::optional<Secp256k1Pubkey> verify_receiver_key_registration(
    uint256_be_t const &chain_id, Address const &validator_address,
    byte_string_fixed<48> const &bls_pubkey, Address const &auth_address,
    byte_string_fixed<33> const &public_key, ReceiverKeyProof const &proof)
{
    Secp256k1Pubkey const key{public_key};
    Secp256k1Pubkey const image{proof.image};
    auto const &challenge = proof.challenge;
    auto const &response = proof.response;
    if (!key.is_valid() || !image.is_valid() || !canonical_scalar(challenge) ||
        !canonical_scalar(response)) {
        return std::nullopt;
    }
    auto const negated_challenge =
        challenge == bytes32_t{}
            ? bytes32_t{}
            : store_be_as<bytes32_t>(
                  SECP256K1_SCALAR_ORDER - load_be<uint256_t>(challenge));
    auto const a = reconstruct(
        get_secp_generator(), key.get(), response, negated_challenge);
    if (!a) {
        return std::nullopt;
    }
    auto const base = receiver_key_registration_base(
        chain_id, validator_address, bls_pubkey, auth_address, public_key);
    if (!base) {
        return std::nullopt;
    }
    auto const b = reconstruct(*base, image.get(), response, negated_challenge);
    if (!b) {
        return std::nullopt;
    }
    auto const expected = receiver_key_registration_challenge(
        *base, public_key, proof.image, *a, *b);
    if (expected != challenge) {
        return std::nullopt;
    }
    return key;
}

MONAD_STAKING_NAMESPACE_END
