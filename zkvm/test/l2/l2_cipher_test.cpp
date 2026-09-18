// Copyright (C) 2026 Category Labs, Inc.
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

// End to end over the real construction: encrypt with the sender's side,
// decrypt with the guest's, and check that every way of tampering is rejected
// rather than halting.
//
// No witness and no block are involved, which is the point -- the crypto is
// testable on its own, and it is where a mistake would be silent.

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/poseidon2.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <zkvm/guest/l2_cipher.hpp>
#include <zkvm/guest/l2_cipher_suite.hpp>
#include <zkvm/guest/l2_ecdh.hpp>

#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <cstring>
#include <optional>
#include <span>
#include <string_view>
#include <type_traits>
#include <vector>

using namespace monad;

namespace
{
    // An arbitrary but fixed operator secret. Not a real key and not secret:
    // this is a test.
    L2Scalar operator_sk()
    {
        return L2Scalar{{0x0123456789abcdefULL, 2, 3, 4}};
    }

    L2Scalar sender_r()
    {
        return L2Scalar{{0xfedcba9876543210ULL, 7, 8, 9}};
    }

    L2CipherContext context()
    {
        L2CipherContext ctx{};
        ctx.version = 1;
        ctx.chain_id = 1;
        ctx.contract = 0x00000000000000000000000000000000cafef00d_address;
        ctx.namespace_id = 42;
        ctx.epoch = 7;
        auto const pk = l2_ecdh(operator_sk(), SECP256K1_G);
        MONAD_ASSERT(pk.has_value());
        l2_point_compress(*pk, std::span<unsigned char, 33>{ctx.operator_pk});
        ctx.constants_digest = l2_constants_digest(ctx);
        return ctx;
    }

    std::array<unsigned char, 16> nonce_of(unsigned char const seed)
    {
        std::array<unsigned char, 16> n{};
        for (size_t i = 0; i < n.size(); ++i) {
            n[i] = static_cast<unsigned char>(seed + i);
        }
        return n;
    }

    std::vector<unsigned char> message(size_t const len)
    {
        std::vector<unsigned char> m(len);
        for (size_t i = 0; i < len; ++i) {
            m[i] = static_cast<unsigned char>(i * 7 + 1);
        }
        return m;
    }
}

TEST(L2Cipher, OperatorKeyBinding)
{
    auto const ctx = context();
    EXPECT_TRUE(l2_check_operator_key(ctx, operator_sk()));
    // A prover supplying any other secret must not be able to proceed: this is
    // the check without which the whole proof is vacuous.
    L2Scalar other = operator_sk();
    other.limb[0] ^= 1u;
    EXPECT_FALSE(l2_check_operator_key(ctx, other));
}

// The lengths that matter: empty, either side of one element, either side of a
// sponge rate block, and something long.
TEST(L2Cipher, RoundTrip)
{
    auto const ctx = context();
    auto const n = nonce_of(0x5a);
    for (size_t len : {0u, 1u, 6u, 7u, 8u, 83u, 84u, 85u, 1000u}) {
        auto const plain = message(len);
        std::vector<unsigned char> leaf;
        ASSERT_TRUE(l2_encrypt_leaf(ctx, sender_r(), n, plain, leaf))
            << "len " << len;
        EXPECT_EQ(leaf.size(), l2_leaf_size(len)) << "len " << len;

        std::vector<unsigned char> got;
        ASSERT_TRUE(l2_decrypt_leaf(ctx, operator_sk(), leaf, got))
            << "len " << len;
        EXPECT_EQ(got, plain) << "len " << len;
    }
}

// The ciphertext must not be the plaintext. Obvious, and exactly the kind of
// thing a masking bug leaves in place.
TEST(L2Cipher, CiphertextDoesNotContainPlaintext)
{
    auto const ctx = context();
    auto const plain = message(64);
    std::vector<unsigned char> leaf;
    ASSERT_TRUE(l2_encrypt_leaf(ctx, sender_r(), nonce_of(1), plain, leaf));
    std::string_view const hay{
        reinterpret_cast<char const *>(leaf.data()), leaf.size()};
    std::string_view const needle{
        reinterpret_cast<char const *>(plain.data()), plain.size()};
    EXPECT_EQ(hay.find(needle), std::string_view::npos);
}

TEST(L2Cipher, DifferentNoncesGiveDifferentLeaves)
{
    auto const ctx = context();
    auto const plain = message(40);
    std::vector<unsigned char> a;
    std::vector<unsigned char> b;
    ASSERT_TRUE(l2_encrypt_leaf(ctx, sender_r(), nonce_of(1), plain, a));
    ASSERT_TRUE(l2_encrypt_leaf(ctx, sender_r(), nonce_of(2), plain, b));
    EXPECT_NE(a, b);
}

// Every field of A is bound by the tag, so a leaf built under one context must
// not verify under a neighbouring one.
TEST(L2Cipher, ContextIsBound)
{
    auto const ctx = context();
    auto const plain = message(30);
    std::vector<unsigned char> leaf;
    ASSERT_TRUE(l2_encrypt_leaf(ctx, sender_r(), nonce_of(3), plain, leaf));

    // The digest is re-derived, which is the whole point: perturbing a field
    // without re-deriving would leave the tag intact and the leaf would
    // decrypt, so this asserts the constants are bound THROUGH the digest.
    auto expect_reject = [&](L2CipherContext other) {
        other.constants_digest = l2_constants_digest(other);
        std::vector<unsigned char> got;
        EXPECT_FALSE(l2_decrypt_leaf(other, operator_sk(), leaf, got));
    };
    {
        auto c = ctx;
        c.version ^= 1u;
        expect_reject(c);
    }
    {
        auto c = ctx;
        c.chain_id ^= 1u;
        expect_reject(c);
    }
    {
        auto c = ctx;
        c.namespace_id ^= 1u;
        expect_reject(c);
    }
    {
        auto c = ctx;
        c.epoch ^= 1u;
        expect_reject(c);
    }
    {
        auto c = ctx;
        c.contract.bytes[19] ^= 1u;
        expect_reject(c);
    }
}

// Tampering is a rejection of one entry, never a halt -- every one of these
// must return false and leave the block valid.
TEST(L2Cipher, TamperingIsRejected)
{
    auto const ctx = context();
    auto const plain = message(50);
    std::vector<unsigned char> base;
    ASSERT_TRUE(l2_encrypt_leaf(ctx, sender_r(), nonce_of(9), plain, base));

    auto reject = [&](std::vector<unsigned char> leaf, char const *what) {
        std::vector<unsigned char> got;
        EXPECT_FALSE(l2_decrypt_leaf(ctx, operator_sk(), leaf, got)) << what;
    };

    { // a flipped ciphertext bit
        auto l = base;
        l[L2_LEAF_C_OFFSET] ^= 1u;
        reject(l, "ciphertext bit");
    }
    { // a flipped tag bit
        auto l = base;
        l.back() ^= 1u;
        reject(l, "tag bit");
    }
    { // a flipped nonce bit -- bound through A
        auto l = base;
        l[L2_LEAF_NONCE_OFFSET] ^= 1u;
        reject(l, "nonce bit");
    }
    { // a declared length that no longer matches the element count
        auto l = base;
        l[L2_LEAF_LEN_OFFSET + 3] ^= 0xffu;
        reject(l, "declared length");
    }
    { // R moved off the curve
        auto l = base;
        l[L2_LEAF_R_OFFSET + 1] ^= 0xffu;
        reject(l, "R x-coordinate");
    }
    { // an R tag byte that is neither 0x02 nor 0x03
        auto l = base;
        l[L2_LEAF_R_OFFSET] = 0x04;
        reject(l, "R parity tag");
    }
    { // truncated
        auto l = base;
        l.pop_back();
        reject(l, "truncated");
    }
    { // shorter than the fixed overhead
        reject(std::vector<unsigned char>(L2_LEAF_OVERHEAD - 1, 0), "stub");
    }
    { // empty
        reject({}, "empty");
    }
    { // a non-canonical ciphertext element, which the sponge could not absorb
        auto l = base;
        for (size_t b = 0; b < 8; ++b) {
            l[L2_LEAF_C_OFFSET + b] = 0xff;
        }
        reject(l, "non-canonical element");
    }
    { // the right leaf under the wrong secret
        std::vector<unsigned char> got;
        L2Scalar wrong = operator_sk();
        wrong.limb[0] ^= 1u;
        EXPECT_FALSE(l2_decrypt_leaf(ctx, wrong, base, got));
    }
}

// This file tests the scheme through its free functions; the guest reaches it
// only through L2EcdhPoseidon2 (l2_cipher_suite.hpp). So the two have to be the
// same thing, or everything above is testing code the guest does not run.
TEST(L2Cipher, SuiteAgreesWithTheFreeFunctions)
{
    static_assert(
        L2CipherSuite<L2EcdhPoseidon2>,
        "this file's scheme no longer satisfies the interface the guest uses");
    static_assert(
        std::is_same_v<L2EcdhPoseidon2, L2Cipher>,
        "a build where this is not the selected suite would test one scheme "
        "and prove another");

    auto const ctx = context();
    std::array<unsigned char, 32> be{};
    L2Scalar const sk = operator_sk();
    for (size_t limb = 0; limb < 4; ++limb) {
        for (size_t b = 0; b < 8; ++b) {
            be[8 * (3 - limb) + (7 - b)] =
                static_cast<unsigned char>(sk.limb[limb] >> (8u * b));
        }
    }

    auto const secret = L2EcdhPoseidon2::bind_secret(
        ctx, std::span<unsigned char const, 32>{be});
    ASSERT_TRUE(secret.has_value())
        << "bind_secret must accept the big-endian form of the operator key";
    EXPECT_EQ(*secret, sk) << "and parse it to the same scalar";

    auto const plain = message(10);
    std::vector<unsigned char> leaf;
    ASSERT_TRUE(l2_encrypt_leaf(ctx, sender_r(), nonce_of(11), plain, leaf));

    std::vector<unsigned char> via_suite;
    std::vector<unsigned char> via_free;
    EXPECT_TRUE(L2EcdhPoseidon2::decrypt(ctx, *secret, leaf, via_suite));
    EXPECT_TRUE(l2_decrypt_leaf(ctx, sk, leaf, via_free));
    EXPECT_EQ(via_suite, via_free);
    EXPECT_EQ(via_suite, plain);

    EXPECT_FALSE(L2EcdhPoseidon2::LABEL.empty())
        << "the sponge asserts a non-empty label";
}

TEST(L2Cipher, LeafSizeArithmetic)
{
    EXPECT_EQ(l2_elem_count(0), 0u);
    EXPECT_EQ(l2_elem_count(1), 1u);
    EXPECT_EQ(l2_elem_count(7), 1u);
    EXPECT_EQ(l2_elem_count(8), 2u);
    EXPECT_EQ(l2_leaf_size(0), L2_LEAF_OVERHEAD);
    EXPECT_EQ(l2_leaf_size(7), L2_LEAF_OVERHEAD + 8u);
}
