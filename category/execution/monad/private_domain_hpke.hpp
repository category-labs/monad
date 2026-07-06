// Copyright (C) 2026 Category Labs, Inc.
// SPDX-License-Identifier: GPL-3.0-or-later

#pragma once

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>

#include <cstdint>
#include <filesystem>
#include <initializer_list>
#include <memory>
#include <optional>
#include <span>
#include <vector>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

struct evp_pkey_st;

MONAD_NAMESPACE_BEGIN

enum class PrivateDomainHpkeError
{
    Success = 0,
    InvalidConfiguration,
    KeyLoadFailed,
    InvalidPrivateKey,
    HpkeUnavailable,
    DecryptionFailed,
};

struct PrivateDomainConfig
{
    uint64_t domain_chain_id;
    Address spoke_address;
    std::filesystem::path private_key_path;
};

// Owns one immutable RFC 9180 receiver key per configured private domain.
class PrivateDomainKeyring
{
    struct PrivateKeyDeleter
    {
        void operator()(evp_pkey_st *) const noexcept;
    };

    using PrivateKeyPtr = std::unique_ptr<evp_pkey_st, PrivateKeyDeleter>;

    std::vector<uint64_t> domain_ids_;
    std::vector<Address> spoke_addresses_;
    std::vector<PrivateKeyPtr> keys_;

public:
    PrivateDomainKeyring() = default;

    [[nodiscard]] std::span<uint64_t const> domain_ids() const noexcept;

    [[nodiscard]] std::optional<Address>
    spoke_address(uint64_t domain_chain_id) const noexcept;

    // Outer payload format: enc (65-byte uncompressed SEC1 point) followed by
    // AES-128-GCM ciphertext and tag. The authenticated plaintext is framed as
    // 0x01 || signed EIP-2718 transaction bytes.
    [[nodiscard]] Result<byte_string>
    decrypt(uint64_t domain_chain_id, byte_string_view payload) const;

    // Load one unencrypted P-256 private key for each domain.
    [[nodiscard]] static Result<PrivateDomainKeyring>
    load(std::span<PrivateDomainConfig const> configs);
};

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::PrivateDomainHpkeError>
    : quick_status_code_from_enum_defaults<monad::PrivateDomainHpkeError>
{
    static constexpr auto const domain_name = "Private Domain HPKE Error";
    static constexpr auto const domain_uuid =
        "260b26da-864f-43c8-ae63-33207ca53dad";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
