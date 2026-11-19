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

// AWS libcrypto's global symbols are linked under an `AWS_` prefix, so each
// function used here is renamed, before the headers declare it. See the AWS
// libcrypto name mangling section of
// category/execution/ethereum/precompiles_impl.hpp.
#define MONAD_AWS_PRAGMA(x) _Pragma(#x)
#define MONAD_AWS_RENAME(name)                                                 \
    MONAD_AWS_PRAGMA(redefine_extname name AWS_##name)

MONAD_AWS_RENAME(BIO_free)
MONAD_AWS_RENAME(BIO_new_file)

MONAD_AWS_RENAME(ERR_clear_error)
MONAD_AWS_RENAME(ERR_get_error)

MONAD_AWS_RENAME(EVP_HPKE_CTX_free)
MONAD_AWS_RENAME(EVP_HPKE_CTX_new)
MONAD_AWS_RENAME(EVP_HPKE_CTX_open)
MONAD_AWS_RENAME(EVP_HPKE_CTX_setup_recipient)

MONAD_AWS_RENAME(EVP_HPKE_KEY_free)
MONAD_AWS_RENAME(EVP_HPKE_KEY_init)
MONAD_AWS_RENAME(EVP_HPKE_KEY_new)

MONAD_AWS_RENAME(EVP_PKEY_free)
MONAD_AWS_RENAME(EVP_PKEY_get_raw_private_key)
MONAD_AWS_RENAME(EVP_PKEY_id)

MONAD_AWS_RENAME(EVP_hpke_aes_128_gcm)
MONAD_AWS_RENAME(EVP_hpke_hkdf_sha256)
MONAD_AWS_RENAME(EVP_hpke_x25519_hkdf_sha256)

MONAD_AWS_RENAME(OPENSSL_cleanse)

MONAD_AWS_RENAME(PEM_read_bio_PrivateKey)

#undef MONAD_AWS_RENAME
#undef MONAD_AWS_PRAGMA

#include <category/execution/domain/hpke.hpp>

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>

#include <boost/outcome/try.hpp>

#include <openssl/base.h>
#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/hpke.h>
#include <openssl/mem.h>
#include <openssl/pem.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <initializer_list>
#include <string_view>
#include <utility>

MONAD_DOMAIN_NAMESPACE_BEGIN

// RFC 9180 Base mode with DHKEM(X25519, HKDF-SHA256), HKDF-SHA256 and
// AES-128-GCM, through AWS-LC's HPKE implementation.
namespace
{
    constexpr uint8_t FRAME_VERSION = 0x01;
    constexpr std::string_view TRANSACTION_AD_LABEL =
        "monad-transaction-encryption-v1";

    constexpr size_t KEY_SIZE = 32; // X25519 private and public keys
    constexpr size_t TAG_SIZE = 16;
    constexpr size_t MIN_PAYLOAD_SIZE = KEY_SIZE + 1 + TAG_SIZE;

    // AWS-LC reads 0 as an empty password, so refuse with a negative value.
    int reject_password(char *, int, int, void *)
    {
        return -1;
    }

    // Reports a failed AWS-LC call as a decryption failure, unless the call
    // ran out of memory. That says nothing about the payload, and derivation
    // drops a transaction that does not open, so a node that carried on would
    // derive a different block than the others from the same L1 inputs.
    Result<byte_string> decryption_failed()
    {
        // Invalid keys and tags are attacker-controlled. Draining the
        // thread-local error queue also keeps their details out of it.
        while (uint32_t const error = ERR_get_error()) {
            MONAD_ASSERT(
                ERR_GET_REASON(error) != ERR_R_MALLOC_FAILURE,
                "allocation failed while opening a private domain transaction");
        }
        return PrivateDomainHpkeError::DecryptionFailed;
    }

    Result<byte_string> hpke_base_open(
        EVP_HPKE_KEY const &recipient, byte_string_view const enc,
        byte_string_view const info, byte_string_view const aad,
        byte_string_view const ciphertext)
    {
        // Start from an empty error queue, so that decryption_failed() reads
        // only the errors of the calls below.
        ERR_clear_error();
        bssl::UniquePtr<EVP_HPKE_CTX> const context{EVP_HPKE_CTX_new()};
        MONAD_ASSERT(context, "failed to allocate an HPKE context");
        // Setup fails on an enc of the wrong size or one that yields an
        // all-zero shared secret.
        if (MONAD_UNLIKELY(
                EVP_HPKE_CTX_setup_recipient(
                    context.get(),
                    &recipient,
                    EVP_hpke_hkdf_sha256(),
                    EVP_hpke_aes_128_gcm(),
                    enc.data(),
                    enc.size(),
                    info.data(),
                    info.size()) != 1)) {
            return decryption_failed();
        }
        byte_string plaintext(ciphertext.size(), 0);
        size_t plaintext_size = 0;
        if (MONAD_UNLIKELY(
                EVP_HPKE_CTX_open(
                    context.get(),
                    plaintext.data(),
                    &plaintext_size,
                    plaintext.size(),
                    ciphertext.data(),
                    ciphertext.size(),
                    aad.data(),
                    aad.size()) != 1)) {
            OPENSSL_cleanse(plaintext.data(), plaintext.size());
            return decryption_failed();
        }
        plaintext.resize(plaintext_size);
        return plaintext;
    }

    Result<bssl::UniquePtr<EVP_HPKE_KEY>>
    make_key(byte_string_view const private_key)
    {
        bssl::UniquePtr<EVP_HPKE_KEY> key{EVP_HPKE_KEY_new()};
        if (!key || EVP_HPKE_KEY_init(
                        key.get(),
                        EVP_hpke_x25519_hkdf_sha256(),
                        private_key.data(),
                        private_key.size()) != 1) {
            ERR_clear_error();
            return PrivateDomainHpkeError::InvalidPrivateKey;
        }
        return key;
    }

    Result<bssl::UniquePtr<EVP_HPKE_KEY>>
    load_private_key(std::filesystem::path const &path)
    {
        auto const null_terminated_path = path.string();
        bssl::UniquePtr<BIO> const input{
            BIO_new_file(null_terminated_path.c_str(), "rb")};
        if (!input) {
            ERR_clear_error();
            return PrivateDomainHpkeError::KeyLoadFailed;
        }

        bssl::UniquePtr<EVP_PKEY> const pkey{PEM_read_bio_PrivateKey(
            input.get(), nullptr, reject_password, nullptr)};
        if (!pkey) {
            ERR_clear_error();
            return PrivateDomainHpkeError::KeyLoadFailed;
        }

        std::array<uint8_t, KEY_SIZE> raw{};
        size_t raw_size = raw.size();
        if (EVP_PKEY_id(pkey.get()) != EVP_PKEY_X25519 ||
            EVP_PKEY_get_raw_private_key(pkey.get(), raw.data(), &raw_size) !=
                1 ||
            raw_size != KEY_SIZE) {
            OPENSSL_cleanse(raw.data(), raw.size());
            ERR_clear_error();
            return PrivateDomainHpkeError::InvalidPrivateKey;
        }
        auto key = make_key({raw.data(), raw.size()});
        OPENSSL_cleanse(raw.data(), raw.size());
        return key;
    }
}

namespace detail
{
    Result<byte_string> hpke_base_open_x25519(
        byte_string_view const private_key, byte_string_view const enc,
        byte_string_view const info, byte_string_view const aad,
        byte_string_view const ciphertext)
    {
        BOOST_OUTCOME_TRY(auto const key, make_key(private_key));
        return hpke_base_open(*key, enc, info, aad, ciphertext);
    }
}

void PrivateDomainKey::PrivateKeyDeleter::operator()(
    evp_hpke_key_st *const key) const noexcept
{
    EVP_HPKE_KEY_free(key);
}

PrivateDomainKey::PrivateDomainKey(PrivateKeyPtr key)
    : key_{std::move(key)}
{
}

byte_string private_domain_transaction_ad(uint64_t const domain_chain_id)
{
    // abi.encode(string label, uint64 domain_chain_id)
    AbiEncoder encoder;
    encoder.add_bytes(
        {reinterpret_cast<uint8_t const *>(TRANSACTION_AD_LABEL.data()),
         TRANSACTION_AD_LABEL.size()});
    encoder.add_uint(u64_be{domain_chain_id});
    return encoder.encode_final();
}

Result<byte_string> PrivateDomainKey::open_transaction(
    uint64_t const domain_chain_id, byte_string_view const payload) const
{
    if (MONAD_UNLIKELY(payload.size() < MIN_PAYLOAD_SIZE)) {
        return PrivateDomainHpkeError::DecryptionFailed;
    }

    BOOST_OUTCOME_TRY(
        auto plaintext,
        hpke_base_open(
            *key_,
            payload.substr(0, KEY_SIZE),
            {},
            private_domain_transaction_ad(domain_chain_id),
            payload.substr(KEY_SIZE)));
    if (MONAD_UNLIKELY(plaintext.empty() || plaintext[0] != FRAME_VERSION)) {
        OPENSSL_cleanse(plaintext.data(), plaintext.size());
        return PrivateDomainHpkeError::DecryptionFailed;
    }
    plaintext.erase(plaintext.begin());
    return plaintext;
}

Result<PrivateDomainKey>
PrivateDomainKey::load(std::filesystem::path const &path)
{
    BOOST_OUTCOME_TRY(auto key, load_private_key(path));
    return PrivateDomainKey{PrivateKeyPtr{key.release()}};
}

MONAD_DOMAIN_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<quick_status_code_from_enum<
    monad::domain::PrivateDomainHpkeError>::mapping> const &
quick_status_code_from_enum<
    monad::domain::PrivateDomainHpkeError>::value_mappings()
{
    using monad::domain::PrivateDomainHpkeError;
    static std::initializer_list<mapping> const mappings = {
        {PrivateDomainHpkeError::Success, "success", {errc::success}},
        {PrivateDomainHpkeError::KeyLoadFailed,
         "failed to load private domain key",
         {errc::io_error}},
        {PrivateDomainHpkeError::InvalidPrivateKey,
         "invalid private domain X25519 key",
         {errc::invalid_argument}},
        {PrivateDomainHpkeError::DecryptionFailed, "decryption failed", {}}};
    return mappings;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
