#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>

#include <blst.h>

MONAD_NAMESPACE_BEGIN

class Bls_Pubkey
{
    blst_p1_affine pubkey_;
    BLST_ERROR parse_result_;

public:
    Bls_Pubkey(byte_string_fixed<48> const &serialized)
    {
        parse_result_ = blst_p1_deserialize(&pubkey_, serialized.data());
    }

    bool is_valid() const noexcept
    {
        // NOTE: deserializing already checks the point is on the curve
        return parse_result_ == BLST_SUCCESS &&
               !blst_p1_affine_is_inf(&pubkey_);
    }

    blst_p1_affine const &get() const noexcept
    {
        return pubkey_;
    }
};

class Bls_Signature
{
    static constexpr char BLS_SIGNATURE_DST[] =
        "BLS_SIG_BLS12381G1_XMD:SHA-256_SSWU_RO_POP_";
    blst_p2_affine sig_;
    BLST_ERROR parse_result_;

public:
    Bls_Signature(byte_string_view const serialized)
    {
        parse_result_ = blst_p2_deserialize(&sig_, serialized.data());
    }

    bool is_valid() const noexcept
    {
        // NOTE: deserializing already checks the point is on the curve
        return parse_result_ == BLST_SUCCESS && !blst_p2_affine_is_inf(&sig_);
    }

    bool verify(Bls_Pubkey const &pubkey, byte_string_view const message)
    {
        BLST_ERROR valid_signature = blst_core_verify_pk_in_g1(
            &pubkey.get(), // Public key in G1
            &sig_, // Signature in G2
            true, // hash-to-curve
            message.data(),
            message.size(),
            reinterpret_cast<uint8_t const *>(BLS_SIGNATURE_DST), // Default DST
            sizeof(BLS_SIGNATURE_DST), // DST length
            nullptr, // No augmentation
            0 // Aug length
        );
        return valid_signature == BLST_SUCCESS;
    }
};

MONAD_NAMESPACE_END
