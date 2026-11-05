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

#include <category/execution/domain/hpke.hpp>

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
using namespace monad::domain;

namespace
{
    constexpr uint64_t DOMAIN_A = 0x510000004eaf;
    constexpr uint64_t DOMAIN_B = 0x520000004eaf;

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
    // X25519_PRIVATE_KEY_1, encrypted with an empty password.
    constexpr std::string_view X25519_EMPTY_PASSWORD_PRIVATE_KEY =
        R"(-----BEGIN ENCRYPTED PRIVATE KEY-----
MIGjMF8GCSqGSIb3DQEFDTBSMDEGCSqGSIb3DQEFDDAkBBDUk+N+iWi0oBq5vgl3
e13iAgIIADAMBggqhkiG9w0CCQUAMB0GCWCGSAFlAwQBKgQQbGgUoHEQ7Yx7FI0M
CbOkzQRAQr46VfMcnNKVL4ktFnAAtjkWPkMaSsK5R+L6AxgEYgsfRbOLxmPY3XKy
RcfDqtRrupsMHJWjwWSvT7z6l87fgw==
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

    // Throws if the key does not load.
    PrivateDomainKey load_key(
        TempDirectory const &directory,
        std::string_view const key = X25519_PRIVATE_KEY_1)
    {
        return PrivateDomainKey::load(directory.write("domain.pem", key))
            .value();
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
    auto const key = load_key(directory);

    auto result = key.open_transaction(DOMAIN_A, independent_payload());

    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result.value(), (byte_string{0x02, 0xc0}));
}

TEST(PrivateDomainHpke, rejects_tampering_and_the_wrong_key)
{
    TempDirectory const directory;
    auto const key = load_key(directory);
    auto tampered = independent_payload();
    tampered.back() ^= 1;

    EXPECT_EQ(
        key.open_transaction(DOMAIN_A, tampered).assume_error(),
        PrivateDomainHpkeError::DecryptionFailed);

    TempDirectory const wrong_key_directory;
    auto const wrong_key = load_key(wrong_key_directory, X25519_PRIVATE_KEY_2);
    EXPECT_EQ(
        wrong_key.open_transaction(DOMAIN_A, independent_payload())
            .assume_error(),
        PrivateDomainHpkeError::DecryptionFailed);
}

// The associated data names the domain, so a transaction sealed for one
// domain does not open in another, even under the same key.
TEST(PrivateDomainHpke, binds_transactions_to_their_domain)
{
    TempDirectory const directory;
    auto const key = load_key(directory);

    EXPECT_TRUE(
        key.open_transaction(DOMAIN_A, independent_payload()).has_value());
    EXPECT_EQ(
        key.open_transaction(DOMAIN_B, independent_payload()).assume_error(),
        PrivateDomainHpkeError::DecryptionFailed);
}

TEST(PrivateDomainHpke, rejects_structurally_invalid_payloads)
{
    TempDirectory const directory;
    auto const key = load_key(directory);

    // Shorter than enc, a frame byte and a tag; then all-zero.
    for (byte_string const &payload :
         {byte_string{}, byte_string(48, 0), byte_string(49, 0)}) {
        auto const result = key.open_transaction(DOMAIN_A, payload);
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(
            result.assume_error(), PrivateDomainHpkeError::DecryptionFailed);
    }

    // A low-order enc yields an all-zero shared secret, which X25519 rejects.
    auto low_order = independent_payload();
    std::ranges::fill(low_order.begin(), low_order.begin() + 32, 0);
    EXPECT_EQ(
        key.open_transaction(DOMAIN_A, low_order).assume_error(),
        PrivateDomainHpkeError::DecryptionFailed);
}

TEST(PrivateDomainHpke, rejects_unloadable_keys)
{
    TempDirectory const directory;
    auto const present = directory.write("present.pem", X25519_PRIVATE_KEY_1);
    std::vector<std::filesystem::path> const paths{
        directory.write("public.pem", X25519_PUBLIC_KEY),
        directory.write("encrypted.pem", X25519_ENCRYPTED_PRIVATE_KEY),
        directory.write(
            "empty_password.pem", X25519_EMPTY_PASSWORD_PRIVATE_KEY),
        directory.write("malformed.pem", "not a private key"),
        present.string() + ".missing"};

    for (auto const &path : paths) {
        auto const result = PrivateDomainKey::load(path);
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
        auto const result = PrivateDomainKey::load(directory.write(name, key));

        ASSERT_TRUE(result.has_error()) << name;
        EXPECT_EQ(
            result.assume_error(), PrivateDomainHpkeError::InvalidPrivateKey)
            << name;
    }
}
