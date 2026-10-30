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

#include <category/execution/monad/private_domain_hpke.hpp>

#include <category/core/int.hpp>
#include <category/core/likely.h>

#include <boost/outcome/try.hpp>

#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/hpke.h>
#include <openssl/mem.h>
#include <openssl/pem.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <memory>
#include <ranges>
#include <string_view>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

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

    template <typename T, auto Free>
    using OpenSslPtr = std::unique_ptr<T, decltype(Free)>;

    using BioPtr = OpenSslPtr<BIO, BIO_free>;
    using EvpPkeyPtr = OpenSslPtr<EVP_PKEY, EVP_PKEY_free>;
    using HpkeContextPtr = OpenSslPtr<EVP_HPKE_CTX, EVP_HPKE_CTX_free>;
    using HpkeKeyPtr = OpenSslPtr<EVP_HPKE_KEY, EVP_HPKE_KEY_free>;

    int reject_password(char *, int, int, void *)
    {
        return 0;
    }

    Result<byte_string> decryption_failed()
    {
        // Invalid keys and tags are attacker-controlled. Do not leave their
        // details in the thread-local error queue.
        ERR_clear_error();
        return PrivateDomainHpkeError::DecryptionFailed;
    }

    Result<byte_string> hpke_base_open(
        EVP_HPKE_KEY const &recipient, byte_string_view const enc,
        byte_string_view const info, byte_string_view const aad,
        byte_string_view const ciphertext)
    {
        // Setup fails on an enc of the wrong size or one that yields an
        // all-zero shared secret.
        HpkeContextPtr const context{EVP_HPKE_CTX_new(), EVP_HPKE_CTX_free};
        if (MONAD_UNLIKELY(
                !context || EVP_HPKE_CTX_setup_recipient(
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

    Result<HpkeKeyPtr> make_key(byte_string_view const private_key)
    {
        HpkeKeyPtr key{EVP_HPKE_KEY_new(), EVP_HPKE_KEY_free};
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

    Result<HpkeKeyPtr> load_private_key(std::filesystem::path const &path)
    {
        auto const null_terminated_path = path.string();
        BioPtr input{
            BIO_new_file(null_terminated_path.c_str(), "rb"), BIO_free};
        if (!input) {
            ERR_clear_error();
            return PrivateDomainHpkeError::KeyLoadFailed;
        }

        EvpPkeyPtr const pkey{
            PEM_read_bio_PrivateKey(
                input.get(), nullptr, reject_password, nullptr),
            EVP_PKEY_free};
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

void PrivateDomainKeyring::PrivateKeyDeleter::operator()(
    evp_hpke_key_st *const key) const noexcept
{
    EVP_HPKE_KEY_free(key);
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

byte_string private_domain_transaction_ad(uint64_t const domain_chain_id)
{
    // abi.encode(string label, uint64 domain_chain_id): the label's offset,
    // the chain id, then the label's length and its bytes padded to a word.
    static_assert(TRANSACTION_AD_LABEL.size() <= 32);
    byte_string ad(4 * 32, 0);
    ad[31] = 0x40;
    store_be(ad.data() + 32 + 24, domain_chain_id);
    ad[3 * 32 - 1] = static_cast<uint8_t>(TRANSACTION_AD_LABEL.size());
    std::ranges::copy(TRANSACTION_AD_LABEL, ad.begin() + 3 * 32);
    return ad;
}

Result<byte_string> PrivateDomainKeyring::open_transaction(
    uint64_t const domain_chain_id, byte_string_view const payload) const
{
    auto const domain_id =
        std::ranges::lower_bound(domain_ids_, domain_chain_id);
    if (MONAD_UNLIKELY(
            domain_id == domain_ids_.end() || *domain_id != domain_chain_id ||
            payload.size() < MIN_PAYLOAD_SIZE)) {
        return decryption_failed();
    }
    auto const &key = keys_[static_cast<size_t>(
        std::distance(domain_ids_.begin(), domain_id))];

    BOOST_OUTCOME_TRY(
        auto plaintext,
        hpke_base_open(
            *key,
            payload.substr(0, KEY_SIZE),
            {},
            private_domain_transaction_ad(domain_chain_id),
            payload.substr(KEY_SIZE)));
    if (MONAD_UNLIKELY(plaintext.empty() || plaintext[0] != FRAME_VERSION)) {
        OPENSSL_cleanse(plaintext.data(), plaintext.size());
        return decryption_failed();
    }
    plaintext.erase(plaintext.begin());
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
         "invalid private domain X25519 key",
         {errc::invalid_argument}},
        {PrivateDomainHpkeError::DecryptionFailed, "decryption failed", {}}};
    return mappings;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
