#pragma once

#include <monad/config.hpp>
#include <monad/core/blake3.hpp>
#include <monad/core/byte_string.hpp>

#include <secp256k1.h>

MONAD_NAMESPACE_BEGIN

class Secp256k1_Pubkey
{
    secp256k1_context const &context_;
    secp256k1_pubkey pubkey_;
    int parse_result_;

public:
    Secp256k1_Pubkey(
        secp256k1_context &context, byte_string_fixed<33> const &serialized)
        : context_{context}
    {
        parse_result_ = secp256k1_ec_pubkey_parse(
            &context_, &pubkey_, serialized.data(), serialized.size());
    }

    bool is_valid() const noexcept
    {
        return parse_result_ == 1;
    }

    secp256k1_pubkey const &get() const noexcept
    {
        return pubkey_;
    }

    byte_string_fixed<65> serialize() const noexcept
    {
        byte_string_fixed<65> serialized;
        size_t uncompressed_pubkey_size = 65;
        secp256k1_ec_pubkey_serialize(
            &context_,
            serialized.data(),
            &uncompressed_pubkey_size,
            &pubkey_,
            SECP256K1_EC_UNCOMPRESSED);
        MONAD_ASSERT(uncompressed_pubkey_size == serialized.size());
        return serialized;
    }
};

class Secp256k1_Signature
{
    secp256k1_context const &context_;
    secp256k1_ecdsa_signature sig_;
    int parse_result_;

public:
    Secp256k1_Signature(
        secp256k1_context &context, byte_string_fixed<64> const &serialized)
        : context_{context}
    {
        parse_result_ = secp256k1_ecdsa_signature_parse_compact(
            &context_, &sig_, serialized.data());
    }

    bool is_valid() const noexcept
    {
        return parse_result_ == 1;
    }

    bool verify(Secp256k1_Pubkey const &pubkey, byte_string_view const message)
        const noexcept
    {
        bytes32_t const digest = to_bytes(blake3(message));
        int res = secp256k1_ecdsa_verify(
            &context_, &sig_, digest.bytes, &pubkey.get());
        return res == 1;
    }

    secp256k1_ecdsa_signature const &get() const noexcept
    {
        return sig_;
    }
};

MONAD_NAMESPACE_END
