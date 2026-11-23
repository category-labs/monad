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

#pragma once

#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/monad/staking/util/receiver_key.hpp>

#include <blst.h>
#include <optional>
#include <secp256k1.h>

namespace monad::staking::test
{
    std::pair<blst_p1, blst_scalar>
    gen_bls_keypair(bytes32_t secret = bytes32_t{0x1000});

    std::pair<secp256k1_pubkey, bytes32_t>
    gen_secp_keypair(bytes32_t secret = bytes32_t{0x1000});

    byte_string_fixed<33> serialize_secp_pubkey(secp256k1_pubkey const &pubkey);

    byte_string_fixed<64>
    sign_secp(byte_string_view message, bytes32_t const &seckey);

    byte_string_fixed<96>
    sign_bls(byte_string_view message, blst_scalar const &seckey);

    byte_string_fixed<65>
    serialize_secp_pubkey_uncompressed(secp256k1_pubkey const &pubkey);

    ReceiverKeyProof prove_receiver_key_registration(
        uint256_be_t const &chain_id, Address const &validator_address,
        byte_string_fixed<48> const &bls_pubkey, Address const &auth_address,
        bytes32_t const &secret, std::optional<bytes32_t> nonce = std::nullopt);

    struct ValidatorRegistration
    {
        byte_string message;
        byte_string_fixed<64> secp_signature;
        byte_string_fixed<96> bls_signature;
        std::optional<ReceiverKeyProof> receiver_proof;
        Address auth_address;
        Address sign_address;

        byte_string encode() const;
    };

    ValidatorRegistration make_validator_registration(
        Address const &auth_address, uint256_t const &stake,
        uint256_t const &commission = 0, bytes32_t secret = bytes32_t{0x1000},
        bool receiver_enabled = true,
        std::optional<bytes32_t> receiver_secret = std::nullopt);

    std::pair<byte_string, Address> craft_add_validator_input(
        Address const &auth_address, uint256_t const &stake,
        uint256_t const &commission = 0, bytes32_t secret = bytes32_t{0x1000},
        bool receiver_enabled = true);

    byte_string craft_undelegate_input(
        u64_be val_id, uint256_t const &amount, u8_be withdrawal_id);

    byte_string craft_withdraw_input(u64_be val_id, u8_be withdrawal_id);

    byte_string
    craft_change_commission_input(u64_be val_id, uint256_t const &commission);
}
