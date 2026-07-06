// Copyright (C) 2026 Category Labs, Inc.
// SPDX-License-Identifier: GPL-3.0-or-later

#include <category/execution/monad/private_domain_hpke.hpp>

#include <category/core/likely.h>

#include <boost/outcome/try.hpp>

#include <openssl/bio.h>
#include <openssl/crypto.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/hpke.h>
#include <openssl/obj_mac.h>
#include <openssl/objects.h>
#include <openssl/pem.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <filesystem>
#include <memory>
#include <ranges>
#include <string_view>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace
{
    constexpr OSSL_HPKE_SUITE HPKE_SUITE{
        OSSL_HPKE_KEM_ID_P256,
        OSSL_HPKE_KDF_ID_HKDF_SHA256,
        OSSL_HPKE_AEAD_ID_AES_GCM_128};
    constexpr std::string_view HPKE_INFO = "private-domain-hpke-rfc9180-v1";
    constexpr size_t ENCAPSULATED_KEY_SIZE = 65;
    constexpr size_t AEAD_TAG_SIZE = 16;
    constexpr uint8_t FRAME_VERSION = 0x01;
    constexpr size_t MIN_PAYLOAD_SIZE =
        ENCAPSULATED_KEY_SIZE + 1 + AEAD_TAG_SIZE;

    template <typename T, auto Free>
    using OpenSslPtr = std::unique_ptr<T, decltype(Free)>;

    using BioPtr = OpenSslPtr<BIO, BIO_free>;
    using EvpPkeyPtr = OpenSslPtr<EVP_PKEY, EVP_PKEY_free>;
    using EvpPkeyCtxPtr = OpenSslPtr<EVP_PKEY_CTX, EVP_PKEY_CTX_free>;
    using HpkeCtxPtr = OpenSslPtr<OSSL_HPKE_CTX, OSSL_HPKE_CTX_free>;

    int reject_password(char *, int, int, void *)
    {
        return 0;
    }

    Result<EvpPkeyPtr> load_private_key(std::filesystem::path const &path)
    {
        auto const null_terminated_path = path.string();
        BioPtr input{
            BIO_new_file(null_terminated_path.c_str(), "rb"), BIO_free};
        if (!input) {
            ERR_clear_error();
            return PrivateDomainHpkeError::KeyLoadFailed;
        }

        EvpPkeyPtr key{
            PEM_read_bio_PrivateKey_ex(
                input.get(),
                nullptr,
                reject_password,
                nullptr,
                nullptr,
                nullptr),
            EVP_PKEY_free};
        if (!key) {
            ERR_clear_error();
            return PrivateDomainHpkeError::KeyLoadFailed;
        }

        std::array<char, 80> group_name{};
        size_t group_name_size = 0;
        if (EVP_PKEY_is_a(key.get(), "EC") != 1 ||
            EVP_PKEY_get_group_name(
                key.get(),
                group_name.data(),
                group_name.size(),
                &group_name_size) != 1 ||
            OBJ_txt2nid(group_name.data()) != NID_X9_62_prime256v1) {
            ERR_clear_error();
            return PrivateDomainHpkeError::InvalidPrivateKey;
        }

        EvpPkeyCtxPtr check_context{
            EVP_PKEY_CTX_new_from_pkey(nullptr, key.get(), nullptr),
            EVP_PKEY_CTX_free};
        if (!check_context ||
            EVP_PKEY_private_check(check_context.get()) != 1 ||
            EVP_PKEY_pairwise_check(check_context.get()) != 1) {
            ERR_clear_error();
            return PrivateDomainHpkeError::InvalidPrivateKey;
        }

        ERR_clear_error();
        return key;
    }

    Result<byte_string> decryption_failed()
    {
        // Invalid points and tags are attacker-controlled. Do not leave their
        // details in the thread-local OpenSSL error queue.
        ERR_clear_error();
        return PrivateDomainHpkeError::DecryptionFailed;
    }
}

void PrivateDomainKeyring::PrivateKeyDeleter::operator()(
    evp_pkey_st *const key) const noexcept
{
    EVP_PKEY_free(key);
}

std::span<uint64_t const> PrivateDomainKeyring::domain_ids() const noexcept
{
    return domain_ids_;
}

std::optional<Address> PrivateDomainKeyring::spoke_address(
    uint64_t const domain_chain_id) const noexcept
{
    auto const domain_id =
        std::ranges::lower_bound(domain_ids_, domain_chain_id);
    if (domain_id == domain_ids_.end() || *domain_id != domain_chain_id) {
        return std::nullopt;
    }
    return spoke_addresses_[static_cast<size_t>(
        std::distance(domain_ids_.begin(), domain_id))];
}

Result<byte_string> PrivateDomainKeyring::decrypt(
    uint64_t const domain_chain_id, byte_string_view const payload) const
{
    auto const domain_id =
        std::ranges::lower_bound(domain_ids_, domain_chain_id);
    if (MONAD_UNLIKELY(
            domain_id == domain_ids_.end() || *domain_id != domain_chain_id ||
            payload.size() < MIN_PAYLOAD_SIZE || payload[0] != 0x04)) {
        return decryption_failed();
    }
    auto const &key = keys_[static_cast<size_t>(
        std::distance(domain_ids_.begin(), domain_id))];

    byte_string_view const encapsulated_key =
        payload.substr(0, ENCAPSULATED_KEY_SIZE);
    byte_string_view const ciphertext = payload.substr(ENCAPSULATED_KEY_SIZE);
    if (MONAD_UNLIKELY(ciphertext.size() < 1 + AEAD_TAG_SIZE)) {
        return decryption_failed();
    }

    HpkeCtxPtr context{
        OSSL_HPKE_CTX_new(
            OSSL_HPKE_MODE_BASE,
            HPKE_SUITE,
            OSSL_HPKE_ROLE_RECEIVER,
            nullptr,
            nullptr),
        OSSL_HPKE_CTX_free};
    if (MONAD_UNLIKELY(!context)) {
        ERR_clear_error();
        return PrivateDomainHpkeError::HpkeUnavailable;
    }

    if (MONAD_UNLIKELY(
            OSSL_HPKE_decap(
                context.get(),
                encapsulated_key.data(),
                encapsulated_key.size(),
                key.get(),
                reinterpret_cast<unsigned char const *>(HPKE_INFO.data()),
                HPKE_INFO.size()) != 1)) {
        return decryption_failed();
    }

    byte_string plaintext(ciphertext.size(), 0);
    size_t plaintext_size = plaintext.size();
    if (MONAD_UNLIKELY(
            OSSL_HPKE_open(
                context.get(),
                plaintext.data(),
                &plaintext_size,
                nullptr,
                0,
                ciphertext.data(),
                ciphertext.size()) != 1 ||
            plaintext_size < 1 || plaintext[0] != FRAME_VERSION)) {
        OPENSSL_cleanse(plaintext.data(), plaintext.size());
        return decryption_failed();
    }

    plaintext.erase(plaintext.begin());
    plaintext.resize(plaintext_size - 1);
    ERR_clear_error();
    return plaintext;
}

Result<PrivateDomainKeyring>
PrivateDomainKeyring::load(std::span<PrivateDomainConfig const> const configs)
{
    std::vector<PrivateDomainConfig> files{configs.begin(), configs.end()};
    std::ranges::sort(files, {}, &PrivateDomainConfig::domain_chain_id);
    if (std::ranges::adjacent_find(
            files, {}, &PrivateDomainConfig::domain_chain_id) != files.end() ||
        std::ranges::any_of(files, [](PrivateDomainConfig const &config) {
            return config.spoke_address == Address{};
        })) {
        return PrivateDomainHpkeError::InvalidConfiguration;
    }

    PrivateDomainKeyring keyring;
    if (files.empty()) {
        return keyring;
    }
    if (OSSL_HPKE_suite_check(HPKE_SUITE) != 1) {
        ERR_clear_error();
        return PrivateDomainHpkeError::HpkeUnavailable;
    }

    keyring.domain_ids_.reserve(files.size());
    keyring.spoke_addresses_.reserve(files.size());
    keyring.keys_.reserve(files.size());
    for (auto const &file : files) {
        BOOST_OUTCOME_TRY(auto key, load_private_key(file.private_key_path));
        keyring.domain_ids_.push_back(file.domain_chain_id);
        keyring.spoke_addresses_.push_back(file.spoke_address);
        keyring.keys_.push_back(PrivateKeyPtr{key.release()});
    }
    return keyring;
}

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::PrivateDomainHpkeError>::mapping> const &
quick_status_code_from_enum<monad::PrivateDomainHpkeError>::value_mappings()
{
    using monad::PrivateDomainHpkeError;
    static std::initializer_list<mapping> const mappings = {
        {PrivateDomainHpkeError::Success, "success", {errc::success}},
        {PrivateDomainHpkeError::InvalidConfiguration,
         "invalid private domain configuration",
         {errc::invalid_argument}},
        {PrivateDomainHpkeError::KeyLoadFailed,
         "failed to load private domain key",
         {errc::io_error}},
        {PrivateDomainHpkeError::InvalidPrivateKey,
         "invalid private domain P-256 key",
         {errc::invalid_argument}},
        {PrivateDomainHpkeError::HpkeUnavailable,
         "HPKE unavailable",
         {errc::not_supported}},
        {PrivateDomainHpkeError::DecryptionFailed, "decryption failed", {}}};
    return mappings;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
