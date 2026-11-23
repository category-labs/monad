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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/blake3.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/monad/staking/config.hpp>

#include <secp256k1.h>

MONAD_STAKING_NAMESPACE_BEGIN

// SEC 2, version 2.0, Section 2.4.1: n, the order of the base point G.
// Scalar arithmetic is modulo n, independently of the coordinate field modulus.
// https://www.secg.org/sec2-v2.pdf#page=13
inline constexpr uint256_t SECP256K1_SCALAR_ORDER = [] {
    using namespace monad::literals;
    return 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141_u256;
}();

// SEC 2, version 2.0, Section 2.4.1: G in compressed form. The prefix 0x02
// selects its even y-coordinate; the remaining 32 bytes encode its
// x-coordinate. https://www.secg.org/sec2-v2.pdf#page=13
inline constexpr byte_string_fixed<33> SECP256K1_GENERATOR_COMPRESSED{
    0x02, 0x79, 0xbe, 0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac, 0x55, 0xa0,
    0x62, 0x95, 0xce, 0x87, 0x0b, 0x07, 0x02, 0x9b, 0xfc, 0xdb, 0x2d,
    0xce, 0x28, 0xd9, 0x59, 0xf2, 0x81, 0x5b, 0x16, 0xf8, 0x17, 0x98};

Address address_from_secpkey(byte_string_fixed<65> const &);

secp256k1_context const *get_secp_context();

secp256k1_pubkey const &get_secp_generator();

class Secp256k1Pubkey
{
    secp256k1_pubkey pubkey_;
    int parse_result_;

public:
    explicit Secp256k1Pubkey(byte_string_fixed<33> const &serialized)
    {
        parse_result_ = secp256k1_ec_pubkey_parse(
            get_secp_context(), &pubkey_, serialized.data(), serialized.size());
    }

    bool is_valid() const
    {
        return parse_result_ == 1;
    }

    secp256k1_pubkey const &get() const
    {
        return pubkey_;
    }

    byte_string_fixed<65> serialize() const
    {
        byte_string_fixed<65> serialized;
        size_t uncompressed_pubkey_size = 65;
        secp256k1_ec_pubkey_serialize(
            get_secp_context(),
            serialized.data(),
            &uncompressed_pubkey_size,
            &pubkey_,
            SECP256K1_EC_UNCOMPRESSED);
        MONAD_ASSERT(uncompressed_pubkey_size == serialized.size());
        return serialized;
    }
};

class Secp256k1Signature
{
    secp256k1_ecdsa_signature sig_;
    int parse_result_;

public:
    explicit Secp256k1Signature(byte_string_fixed<64> const &serialized)
    {
        parse_result_ = secp256k1_ecdsa_signature_parse_compact(
            get_secp_context(), &sig_, serialized.data());
    }

    bool is_valid() const
    {
        return parse_result_ == 1;
    }

    bool
    verify(Secp256k1Pubkey const &pubkey, byte_string_view const message) const
    {
        bytes32_t const digest = to_bytes(blake3(message));
        int const res = secp256k1_ecdsa_verify(
            get_secp_context(), &sig_, digest.bytes, &pubkey.get());
        return res == 1;
    }

    secp256k1_ecdsa_signature const &get() const
    {
        return sig_;
    }
};

MONAD_STAKING_NAMESPACE_END
