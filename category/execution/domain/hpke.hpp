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

#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>

#include <cstdint>
#include <filesystem>
#include <initializer_list>
#include <memory>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

struct evp_hpke_key_st;

MONAD_DOMAIN_NAMESPACE_BEGIN

enum class PrivateDomainHpkeError
{
    Success = 0,
    KeyLoadFailed,
    InvalidPrivateKey,
    DecryptionFailed,
};

namespace detail
{
    // RFC 9180 single-shot Base-mode open for DHKEM(X25519, HKDF-SHA256),
    // HKDF-SHA256 and AES-128-GCM. `private_key` is the recipient's 32-byte
    // X25519 key and `enc` the sender's 32-byte ephemeral public key. Exposed
    // for the RFC test vectors.
    Result<byte_string> hpke_base_open_x25519(
        byte_string_view private_key, byte_string_view enc,
        byte_string_view info, byte_string_view aad,
        byte_string_view ciphertext);
}

// Associated data a sequenced transaction of `domain_chain_id` is sealed with:
// abi.encode("monad-transaction-encryption-v1", uint64 domain_chain_id).
byte_string private_domain_transaction_ad(uint64_t domain_chain_id);

// One private domain's RFC 9180 receiver key.
class PrivateDomainKey
{
    struct PrivateKeyDeleter
    {
        void operator()(evp_hpke_key_st *) const noexcept;
    };

    using PrivateKeyPtr = std::unique_ptr<evp_hpke_key_st, PrivateKeyDeleter>;

    PrivateKeyPtr key_;

    explicit PrivateDomainKey(PrivateKeyPtr);

public:
    // Opens one sequenced transaction of `domain_chain_id` sealed to this key
    // and strips its frame byte. `payload` is enc (the 32-byte X25519
    // ephemeral public key) followed by the AES-128-GCM ciphertext and tag;
    // the sealed plaintext is 0x01 || signed EIP-2718 transaction, with empty
    // info and private_domain_transaction_ad(domain_chain_id) as associated
    // data.
    [[nodiscard]] Result<byte_string>
    open_transaction(uint64_t domain_chain_id, byte_string_view payload) const;

    // Loads an unencrypted X25519 private key (PKCS#8 PEM).
    [[nodiscard]] static Result<PrivateDomainKey>
    load(std::filesystem::path const &);
};

MONAD_DOMAIN_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::domain::PrivateDomainHpkeError>
    : quick_status_code_from_enum_defaults<
          monad::domain::PrivateDomainHpkeError>
{
    static constexpr auto const domain_name = "Private Domain HPKE Error";
    static constexpr auto const domain_uuid =
        "260b26da-864f-43c8-ae63-33207ca53dad";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
