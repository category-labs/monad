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

#pragma once

#include <category/core/result.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/monad/staking/util/secp256k1.hpp>

#include <optional>

MONAD_STAKING_NAMESPACE_BEGIN

// BTX DKG specification, Section 2.1: BVE.PoPVerify.
// ABI tuple (bytes image, bytes32 challenge, bytes32 response). Admission
// requires image to contain exactly 33 bytes before constructing this value.
struct ReceiverKeyProof
{
    byte_string_fixed<33> image;
    bytes32_t challenge;
    bytes32_t response;
};

Result<ReceiverKeyProof> decode_receiver_key_proof(byte_string_view &input);

std::optional<secp256k1_pubkey> receiver_key_registration_base(
    uint256_be_t const &chain_id, Address const &validator_address,
    byte_string_fixed<48> const &bls_pubkey, Address const &auth_address,
    byte_string_fixed<33> const &public_key);

bytes32_t receiver_key_registration_challenge(
    secp256k1_pubkey const &base, byte_string_fixed<33> const &public_key,
    byte_string_fixed<33> const &image, secp256k1_pubkey const &a,
    secp256k1_pubkey const &b);

// Return the parsed receiver key on success for use by the ownership lookup.
std::optional<Secp256k1Pubkey> verify_receiver_key_registration(
    uint256_be_t const &chain_id, Address const &validator_address,
    byte_string_fixed<48> const &bls_pubkey, Address const &auth_address,
    byte_string_fixed<33> const &public_key, ReceiverKeyProof const &proof);

MONAD_STAKING_NAMESPACE_END
