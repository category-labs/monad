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

#include <category/core/byte_string.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/monad/staking/config.hpp>

#include <blst.h>

MONAD_STAKING_NAMESPACE_BEGIN

Address address_from_bls_key(byte_string_fixed<96> const &);

class BlsPubkey
{
    blst_p1_affine pubkey_;
    BLST_ERROR parse_result_;

public:
    BlsPubkey(byte_string_fixed<48> const &compressed)
    {
        parse_result_ = blst_p1_uncompress(&pubkey_, compressed.data());
    }

    bool is_valid() const noexcept
    {
        // NOTE: deserializing already checks the point is on the curve
        return parse_result_ == BLST_SUCCESS &&
               blst_p1_affine_in_g1(&pubkey_) &&
               !blst_p1_affine_is_inf(&pubkey_);
    }

    byte_string_fixed<96> serialize() const noexcept
    {
        byte_string_fixed<96> serialized;
        blst_p1_affine_serialize(serialized.data(), &pubkey_);
        return serialized;
    }

    blst_p1_affine const &get() const noexcept
    {
        return pubkey_;
    }
};

class BlsSignature
{
    static constexpr char BLS_SIGNATURE_DST[] =
        "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_";
    blst_p2_affine sig_;
    BLST_ERROR parse_result_;

public:
    BlsSignature(byte_string_fixed<96> const &compressed)
    {
        parse_result_ = blst_p2_uncompress(&sig_, compressed.data());
    }

    bool is_valid() const noexcept
    {
        // NOTE: deserializing already checks the point is on the curve
        return parse_result_ == BLST_SUCCESS && blst_p2_affine_in_g2(&sig_) &&
               !blst_p2_affine_is_inf(&sig_);
    }

    bool verify(BlsPubkey const &pubkey, byte_string_view const message)
    {
        BLST_ERROR valid_signature = blst_core_verify_pk_in_g1(
            &pubkey.get(), // Public key in G1
            &sig_, // Signature in G2
            true, // hash-to-curve
            message.data(),
            message.size(),
            reinterpret_cast<uint8_t const *>(BLS_SIGNATURE_DST), // Default DST
            sizeof(BLS_SIGNATURE_DST) - 1, // DST length
            nullptr, // No augmentation
            0 // Aug length
        );
        return valid_signature == BLST_SUCCESS;
    }
};

MONAD_STAKING_NAMESPACE_END
