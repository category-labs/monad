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

    constexpr std::string_view X25519_PRIVATE_KEY_1 =
        R"(-----BEGIN PRIVATE KEY-----
MC4CAQAwBQYDK2VuBCIEIBERERERERERERERERERERERERERERERERERERERERER
-----END PRIVATE KEY-----
)";
    constexpr std::string_view X25519_PRIVATE_KEY_2 =
        R"(-----BEGIN PRIVATE KEY-----
MC4CAQAwBQYDK2VuBCIEICIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIi
-----END PRIVATE KEY-----
)";
    constexpr std::string_view X25519_PUBLIC_KEY =
        R"(-----BEGIN PUBLIC KEY-----
MCowBQYDK2VuAyEAe06Qm75//kTEZaIgA31gjuNYl9Me+XLwf3SJLLD3PxM=
-----END PUBLIC KEY-----
)";
    constexpr std::string_view X25519_ENCRYPTED_PRIVATE_KEY =
        R"(-----BEGIN ENCRYPTED PRIVATE KEY-----
MIGjMF8GCSqGSIb3DQEFDTBSMDEGCSqGSIb3DQEFDDAkBBDb4fE0DEUGmlZtdTIe
Gn3bAgIIADAMBggqhkiG9w0CCQUAMB0GCWCGSAFlAwQBKgQQhawEy6jZ/nwwcah6
QUsf+ARAG+PYDVv2hok3nizXq3yxknY4NN6n5aaTMmJ+PZgwhK2hI0PNpONUU+ks
XThzuqMyRL7NY9sNikRrjCx1huYNjw==
-----END ENCRYPTED PRIVATE KEY-----
)";
    constexpr std::string_view P256_PRIVATE_KEY =
        R"(-----BEGIN PRIVATE KEY-----
MIGHAgEAMBMGByqGSM49AgEGCCqGSM49AwEHBG0wawIBAQQgAAAAAAAAAAAAAAAA
AAAAAAAAAAAAAAAAAAAAAAAAAAGhRANCAARrF9Hy4SxCR/i85uVjpEDydwN9gS3r
M6D0oTlF2JjClk/jQuL+Gn+bjufrSnwPnhYrzjNXazFezsu2QGg3v1H1
-----END PRIVATE KEY-----
)";
    constexpr std::string_view SECP256K1_PRIVATE_KEY =
        R"(-----BEGIN PRIVATE KEY-----
MIGEAgEAMBAGByqGSM49AgEGBSuBBAAKBG0wawIBAQQgAAAAAAAAAAAAAAAAAAAA
AAAAAAAAAAAAAAAAAAAAAAGhRANCAAR5vmZ++dy7rFWgYpXOhwsHApv82y3OKNlZ
8oFbFvgXmEg62ncmo8RlXaT7/A4RCKj9F7RIpoVUGZxH0I/7ENS4
-----END PRIVATE KEY-----
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
        std::string_view const key = X25519_PRIVATE_KEY_1)
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
        // pyhpke 0.6.5, X25519_PRIVATE_KEY_1 (0x11 * 32), ephemeral key
        // derived from ikm 0x33 * 32, empty info, the transaction ad of
        // DOMAIN_A, plaintext 0x01 || 02 c0.
        return *from_hex(
            "a04588b74683334f6e7670db45cca1288fc2c1499d78715d9456f5d99261a823"
            "a3c6898d05630de04949dbf70f2e544a52814e");
    }
}

// RFC 9180 Appendix A.1.1: DHKEM(X25519, HKDF-SHA256), HKDF-SHA256,
// AES-128-GCM, Base mode, sequence number 0.
TEST(PrivateDomainHpke, opens_rfc9180_base_vector)
{
    byte_string const sk_r = *from_hex(
        "4612c550263fc8ad58375df3f557aac531d26850903e55a9f23f21d8534e8ac8");
    byte_string const enc = *from_hex(
        "37fda3567bdbd628e88668c3c8d7e97d1d1253b6d4ea6d44c150f741f1bf4431");
    byte_string const info =
        *from_hex("4f6465206f6e2061204772656369616e2055726e");
    byte_string const aad = *from_hex("436f756e742d30");
    byte_string const ct = *from_hex(
        "f938558b5d72f1a23810b4be2ab4f84331acc02fc97babc53a52ae8218a355a9"
        "6d8770ac83d07bea87e13c512a");
    byte_string const pt =
        *from_hex("4265617574792069732074727574682c20747275746820626561757479");

    auto result = detail::hpke_base_open_x25519(sk_r, enc, info, aad, ct);

    ASSERT_TRUE(result.has_value()) << result.assume_error().message().c_str();
    EXPECT_EQ(result.value(), pt);

    auto const wrong_aad =
        detail::hpke_base_open_x25519(sk_r, enc, info, {}, ct);
    ASSERT_TRUE(wrong_aad.has_error());
    EXPECT_EQ(
        wrong_aad.assume_error(), PrivateDomainHpkeError::DecryptionFailed);
}

TEST(PrivateDomainHpke, encodes_transaction_ad)
{
    EXPECT_EQ(
        private_domain_transaction_ad(DOMAIN_A),
        *from_hex(
            "0000000000000000000000000000000000000000000000000000000000000040"
            "0000000000000000000000000000000000000000000000000000510000004eaf"
            "000000000000000000000000000000000000000000000000000000000000001f"
            "6d6f6e61642d7472616e73616374696f6e2d656e6372797074696f6e2d76310"
            "0"));
}

TEST(PrivateDomainHpke, opens_independent_transaction_vector)
{
    TempDirectory const directory;
    auto keyring = load_keyring(directory);

    auto result = keyring.open_transaction(DOMAIN_A, independent_payload());

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
        keyring.open_transaction(DOMAIN_A, tampered).assume_error(),
        PrivateDomainHpkeError::DecryptionFailed);
    EXPECT_EQ(
        keyring.open_transaction(DOMAIN_B, independent_payload())
            .assume_error(),
        PrivateDomainHpkeError::DecryptionFailed);

    TempDirectory const wrong_key_directory;
    auto wrong_keyring =
        load_keyring(wrong_key_directory, X25519_PRIVATE_KEY_2);
    EXPECT_EQ(
        wrong_keyring.open_transaction(DOMAIN_A, independent_payload())
            .assume_error(),
        PrivateDomainHpkeError::DecryptionFailed);
}

TEST(PrivateDomainHpke, binds_transactions_to_their_domain)
{
    TempDirectory const directory;
    auto const path = directory.write("shared.pem", X25519_PRIVATE_KEY_1);
    std::vector<PrivateDomainConfig> const configs{
        {DOMAIN_A, SPOKE_A, path}, {DOMAIN_B, SPOKE_B, path}};
    auto keyring = PrivateDomainKeyring::load(configs);
    ASSERT_TRUE(keyring.has_value());

    EXPECT_TRUE(keyring.value()
                    .open_transaction(DOMAIN_A, independent_payload())
                    .has_value());
    EXPECT_EQ(
        keyring.value()
            .open_transaction(DOMAIN_B, independent_payload())
            .assume_error(),
        PrivateDomainHpkeError::DecryptionFailed);
}

TEST(PrivateDomainHpke, rejects_structurally_invalid_payloads)
{
    TempDirectory const directory;
    auto keyring = load_keyring(directory);

    // Shorter than enc, a frame byte and a tag; then all-zero.
    for (byte_string const &payload :
         {byte_string{}, byte_string(48, 0), byte_string(49, 0)}) {
        auto const result = keyring.open_transaction(DOMAIN_A, payload);
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(
            result.assume_error(), PrivateDomainHpkeError::DecryptionFailed);
    }

    // A low-order enc yields an all-zero shared secret, which X25519 rejects.
    auto low_order = independent_payload();
    std::ranges::fill(low_order.begin(), low_order.begin() + 32, 0);
    EXPECT_EQ(
        keyring.open_transaction(DOMAIN_A, low_order).assume_error(),
        PrivateDomainHpkeError::DecryptionFailed);
}

TEST(PrivateDomainHpke, loads_sorted_unique_domain_mappings)
{
    TempDirectory const directory;
    auto const a = directory.write("a=key.pem", X25519_PRIVATE_KEY_1);
    auto const b = directory.write("b.pem", X25519_PRIVATE_KEY_2);
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
    auto const a = directory.write("a.pem", X25519_PRIVATE_KEY_1);

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
    auto const present = directory.write("present.pem", X25519_PRIVATE_KEY_1);
    std::vector<std::filesystem::path> const paths{
        directory.write("public.pem", X25519_PUBLIC_KEY),
        directory.write("encrypted.pem", X25519_ENCRYPTED_PRIVATE_KEY),
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

TEST(PrivateDomainHpke, rejects_non_x25519_private_keys)
{
    TempDirectory const directory;
    for (auto const &[name, key] :
         {std::pair{"p256.pem", P256_PRIVATE_KEY},
          std::pair{"secp256k1.pem", SECP256K1_PRIVATE_KEY}}) {
        std::vector<PrivateDomainConfig> const configs{
            {DOMAIN_A, SPOKE_A, directory.write(name, key)}};

        auto const result = PrivateDomainKeyring::load(configs);

        ASSERT_TRUE(result.has_error()) << name;
        EXPECT_EQ(
            result.assume_error(), PrivateDomainHpkeError::InvalidPrivateKey)
            << name;
    }
}
