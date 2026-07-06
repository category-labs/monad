// Copyright (C) 2026 Category Labs, Inc.
// SPDX-License-Identifier: GPL-3.0-or-later

#include <category/execution/monad/private_domain_hpke.hpp>

#include <category/core/hex.hpp>

#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <ranges>
#include <span>
#include <string>
#include <string_view>
#include <unistd.h>
#include <utility>
#include <vector>

using namespace monad;

namespace
{
    constexpr uint64_t DOMAIN_A = 0x510000004eaf;
    constexpr uint64_t DOMAIN_B = 0x520000004eaf;
    constexpr Address SPOKE_A =
        0x1111111111111111111111111111111111111111_address;
    constexpr Address SPOKE_B =
        0x2222222222222222222222222222222222222222_address;

    constexpr std::string_view P256_PRIVATE_KEY_1 =
        R"(-----BEGIN PRIVATE KEY-----
MIGHAgEAMBMGByqGSM49AgEGCCqGSM49AwEHBG0wawIBAQQgAAAAAAAAAAAAAAAA
AAAAAAAAAAAAAAAAAAAAAAAAAAGhRANCAARrF9Hy4SxCR/i85uVjpEDydwN9gS3r
M6D0oTlF2JjClk/jQuL+Gn+bjufrSnwPnhYrzjNXazFezsu2QGg3v1H1
-----END PRIVATE KEY-----
)";
    constexpr std::string_view P256_PRIVATE_KEY_2 =
        R"(-----BEGIN PRIVATE KEY-----
MIGHAgEAMBMGByqGSM49AgEGCCqGSM49AwEHBG0wawIBAQQgAAAAAAAAAAAAAAAA
AAAAAAAAAAAAAAAAAAAAAAAAAAKhRANCAAR88nsYjQNPfopSOAMEtRrDwIlp4nfy
GzWmC0j8R2aZeAd3VRDbjtBAKT2axp90MNu6fa3mPOmCKZ4Et50ieHPR
-----END PRIVATE KEY-----
)";
    constexpr std::string_view SECP256K1_PRIVATE_KEY =
        R"(-----BEGIN PRIVATE KEY-----
MIGEAgEAMBAGByqGSM49AgEGBSuBBAAKBG0wawIBAQQgAAAAAAAAAAAAAAAAAAAA
AAAAAAAAAAAAAAAAAAAAAAGhRANCAAR5vmZ++dy7rFWgYpXOhwsHApv82y3OKNlZ
8oFbFvgXmEg62ncmo8RlXaT7/A4RCKj9F7RIpoVUGZxH0I/7ENS4
-----END PRIVATE KEY-----
)";
    constexpr std::string_view P256_PUBLIC_KEY = R"(-----BEGIN PUBLIC KEY-----
MFkwEwYHKoZIzj0CAQYIKoZIzj0DAQcDQgAEaxfR8uEsQkf4vOblY6RA8ncDfYEt
6zOg9KE5RdiYwpZP40Li/hp/m47n60p8D54WK84zV2sxXs7LtkBoN79R9Q==
-----END PUBLIC KEY-----
)";
    constexpr std::string_view P256_ENCRYPTED_PRIVATE_KEY =
        R"(-----BEGIN ENCRYPTED PRIVATE KEY-----
MIH0MF8GCSqGSIb3DQEFDTBSMDEGCSqGSIb3DQEFDDAkBBBLNfwmL83ehvMCZ3Wq
w8ZQAgIIADAMBggqhkiG9w0CCQUAMB0GCWCGSAFlAwQBKgQQCIzN0yoK+q4sW7Ut
RWYuBASBkHrQZ7oMdbhGzTdj6Ut/5PcUYxoNasy/ecbAOWmjcPWg9fyEzUcMHDkv
TVcjCdqbYnXlre0Xyol3K7cXLqhfRysAs634LbY+9R4DfoP8Xm68atHctLwTIQer
IyzKmePEc3dd6nqKPTLlP7gctaF6cO+1hrvQzw4HedAvwbbOv6tlAMBC1L2VLjEW
fwVzE7C2ZQ==
-----END ENCRYPTED PRIVATE KEY-----
)";

    class TempDirectory
    {
        std::filesystem::path path_;

    public:
        TempDirectory()
        {
            std::array<char, 64> pattern{};
            std::ranges::copy(
                std::string_view{"/tmp/monad-hpke-test-XXXXXX"},
                pattern.begin());
            if (char *const result = ::mkdtemp(pattern.data())) {
                path_ = result;
            }
        }

        ~TempDirectory()
        {
            std::error_code error;
            std::filesystem::remove_all(path_, error);
        }

        [[nodiscard]] std::filesystem::path write(
            std::string_view const name, std::string_view const contents) const
        {
            auto const path = path_ / name;
            std::ofstream stream{path, std::ios::binary};
            stream << contents;
            EXPECT_TRUE(stream.good());
            return path;
        }
    };

    PrivateDomainKeyring load_keyring(
        TempDirectory const &directory,
        std::string_view const key = P256_PRIVATE_KEY_1)
    {
        auto const path = directory.write("domain.pem", key);
        std::vector<PrivateDomainConfig> const configs{
            {DOMAIN_A, SPOKE_A, path}};
        auto result = PrivateDomainKeyring::load(configs);
        if (result.has_error()) {
            ADD_FAILURE() << result.assume_error().message().c_str();
        }
        return result.has_value() ? std::move(result).assume_value()
                                  : PrivateDomainKeyring{};
    }

    byte_string independent_payload()
    {
        // Python hpke 0.3.2, receiver scalar 1, ephemeral scalar 3.
        return *from_hex(
            "045ecbe4d1a6330a44c8f7ef951d4bf165e6c6b721efada985fb41661bc6e7fd"
            "6c8734640c4998ff7e374b06ce1a64a2ecd82ab036384fb83d9a79b127a27d50"
            "32eba7a501f8ca3ab09ff62d7579a8911293d367");
    }
}

TEST(PrivateDomainHpke, decrypts_independent_application_vector)
{
    TempDirectory const directory;
    auto keyring = load_keyring(directory);

    auto result = keyring.decrypt(DOMAIN_A, independent_payload());

    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result.value(), (byte_string{0x02, 0xc0}));
}

TEST(PrivateDomainHpke, rejects_tampering_wrong_key_and_unknown_domain)
{
    TempDirectory const directory;
    auto keyring = load_keyring(directory);
    auto tampered = independent_payload();
    tampered.back() ^= 1;

    EXPECT_EQ(
        keyring.decrypt(DOMAIN_A, tampered).assume_error(),
        PrivateDomainHpkeError::DecryptionFailed);
    EXPECT_EQ(
        keyring.decrypt(DOMAIN_B, independent_payload()).assume_error(),
        PrivateDomainHpkeError::DecryptionFailed);

    TempDirectory const wrong_key_directory;
    auto wrong_keyring = load_keyring(wrong_key_directory, P256_PRIVATE_KEY_2);
    EXPECT_EQ(
        wrong_keyring.decrypt(DOMAIN_A, independent_payload()).assume_error(),
        PrivateDomainHpkeError::DecryptionFailed);
}

TEST(PrivateDomainHpke, rejects_structurally_invalid_payloads)
{
    TempDirectory const directory;
    auto keyring = load_keyring(directory);

    for (byte_string const &payload :
         {byte_string{}, byte_string(81, 0), byte_string(82, 0)}) {
        auto const result = keyring.decrypt(DOMAIN_A, payload);
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(
            result.assume_error(), PrivateDomainHpkeError::DecryptionFailed);
    }

    auto off_curve = independent_payload();
    std::ranges::fill(off_curve.begin() + 1, off_curve.begin() + 65, 0);
    EXPECT_EQ(
        keyring.decrypt(DOMAIN_A, off_curve).assume_error(),
        PrivateDomainHpkeError::DecryptionFailed);
}

TEST(PrivateDomainHpke, loads_sorted_unique_domain_mappings)
{
    TempDirectory const directory;
    auto const a = directory.write("a=key.pem", P256_PRIVATE_KEY_1);
    auto const b = directory.write("b.pem", P256_PRIVATE_KEY_2);
    std::vector<PrivateDomainConfig> const configs{
        {DOMAIN_B, SPOKE_B, b}, {DOMAIN_A, SPOKE_A, a}};

    auto result = PrivateDomainKeyring::load(configs);

    ASSERT_TRUE(result.has_value());
    std::array<uint64_t, 2> const expected{DOMAIN_A, DOMAIN_B};
    EXPECT_TRUE(std::ranges::equal(result.value().domain_ids(), expected));
    EXPECT_EQ(result.value().spoke_address(DOMAIN_A), SPOKE_A);
    EXPECT_EQ(result.value().spoke_address(DOMAIN_B), SPOKE_B);
    EXPECT_FALSE(result.value().spoke_address(0).has_value());

    auto empty =
        PrivateDomainKeyring::load(std::span<PrivateDomainConfig const>{});
    ASSERT_TRUE(empty.has_value());
    EXPECT_TRUE(empty.value().domain_ids().empty());
}

TEST(PrivateDomainHpke, rejects_invalid_mappings)
{
    TempDirectory const directory;
    auto const a = directory.write("a.pem", P256_PRIVATE_KEY_1);

    for (std::vector<PrivateDomainConfig> const &configs :
         {std::vector<PrivateDomainConfig>{{DOMAIN_A, Address{}, a}},
          std::vector<PrivateDomainConfig>{
              {DOMAIN_A, SPOKE_A, a}, {DOMAIN_A, SPOKE_B, a}}}) {
        auto const result = PrivateDomainKeyring::load(configs);
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(
            result.assume_error(),
            PrivateDomainHpkeError::InvalidConfiguration);
    }
}

TEST(PrivateDomainHpke, rejects_unloadable_keys)
{
    TempDirectory const directory;
    auto const present = directory.write("present.pem", P256_PRIVATE_KEY_1);
    std::vector<std::filesystem::path> const paths{
        directory.write("public.pem", P256_PUBLIC_KEY),
        directory.write("encrypted.pem", P256_ENCRYPTED_PRIVATE_KEY),
        directory.write("malformed.pem", "not a private key"),
        present.string() + ".missing"};

    for (auto const &path : paths) {
        std::vector<PrivateDomainConfig> const configs{
            {DOMAIN_A, SPOKE_A, path}};
        auto const result = PrivateDomainKeyring::load(configs);
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.assume_error(), PrivateDomainHpkeError::KeyLoadFailed);
    }
}

TEST(PrivateDomainHpke, rejects_non_p256_private_keys)
{
    TempDirectory const directory;
    auto const path = directory.write("secp256k1.pem", SECP256K1_PRIVATE_KEY);
    std::vector<PrivateDomainConfig> const configs{{DOMAIN_A, SPOKE_A, path}};

    auto const result = PrivateDomainKeyring::load(configs);

    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), PrivateDomainHpkeError::InvalidPrivateKey);
}
