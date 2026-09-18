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

// The ECDH backend, and the layout convention it is reached through.
//
// On the host the backend is libsecp256k1, so these are known-answer and
// property tests against it. The cross-check that actually matters -- that
// zisklib and libsecp256k1 agree -- can only run on ZisK, because only there
// is zisklib linked; it is a guest-side artifact, not this file. What this file
// pins is the part that is ours and therefore ours to get wrong: the limb
// layout, the canonicity rule, and the transcribed generator.
//
// The multiples below were computed from the curve equation independently of
// any implementation in this tree.

#include <category/core/bytes.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <zkvm/guest/l2_ecdh.hpp>

#include <gtest/gtest.h>

#include <array>
#include <cstring>
#include <span>

using namespace monad;

namespace
{
    L2Point point_of(bytes32_t const &x, bytes32_t const &y)
    {
        std::array<unsigned char, 64> be{};
        std::memcpy(be.data(), x.bytes, 32);
        std::memcpy(be.data() + 32, y.bytes, 32);
        return l2_point_from_be(std::span<unsigned char const, 64>{be});
    }

    L2Scalar scalar_of(bytes32_t const &v)
    {
        return l2_scalar_from_be(
            std::span<unsigned char const, 32>{v.bytes, 32});
    }

    L2Point const &generator()
    {
        static L2Point const g = point_of(
            0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798_bytes32,
            0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8_bytes32);
        return g;
    }
}

// G as transcribed into l2_ecdh.hpp must be G as spelled in SEC 2. This is the
// one constant in the file with no second source inside the build, so it gets
// one here.
TEST(L2Ecdh, TranscribedGeneratorMatchesSec2)
{
    EXPECT_EQ(SECP256K1_G, generator());
}

TEST(L2Ecdh, SelfTest)
{
    EXPECT_TRUE(l2_ecdh_self_test());
}

TEST(L2Ecdh, KnownMultiples)
{
    auto const g = generator();

    struct
    {
        uint64_t k;
        L2Point want;
    } const cases[] = {
        {2,
         point_of(
             0xc6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5_bytes32,
             0x1ae168fea63dc339a3c58419466ceaeef7f632653266d0e1236431a950cfe52a_bytes32)},
        {3,
         point_of(
             0xf9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9_bytes32,
             0x388f7b0f632de8140fe337e62a37f3566500a99934c2231b6cb9fd7584b8e672_bytes32)},
        {7,
         point_of(
             0x5cbdf0646e5db4eaa398f365f2ea7a0e3d419b7e0330e39ce92bddedcac4f9bc_bytes32,
             0x6aebca40ba255960a3178d6d861a54dba813d0b813fde7b5a5082628087264da_bytes32)},
    };

    for (auto const &c : cases) {
        auto const got = l2_ecdh(L2Scalar{{c.k, 0, 0, 0}}, g);
        ASSERT_TRUE(got.has_value()) << "k = " << c.k;
        EXPECT_EQ(*got, c.want) << "k = " << c.k;
    }
}

// The property the scheme rests on: the guest computes sk*R and the sender
// computed r*pk, and those have to be the same point.
TEST(L2Ecdh, DiffieHellmanAgrees)
{
    auto const sk = scalar_of(
        0x0000000000000000000000000000000000000000000000001234567890abcdef_bytes32);
    auto const r = scalar_of(
        0x000000000000000000000000000000000000000000000000fedcba0987654321_bytes32);

    auto const pk = l2_ecdh(sk, generator()); // operator's public key
    auto const rr = l2_ecdh(r, generator()); // sender's R
    ASSERT_TRUE(pk.has_value() && rr.has_value());

    auto const sender_side = l2_ecdh(r, *pk); // r * pk
    auto const guest_side = l2_ecdh(sk, *rr); // sk * R
    ASSERT_TRUE(sender_side.has_value() && guest_side.has_value());
    EXPECT_EQ(*sender_side, *guest_side);
}

TEST(L2Ecdh, RejectsTheIdentity)
{
    EXPECT_FALSE(l2_point_is_valid(L2Point{}));
    EXPECT_FALSE(l2_ecdh(L2Scalar{{1, 0, 0, 0}}, L2Point{}).has_value());
}

TEST(L2Ecdh, RejectsOffCurve)
{
    auto p = generator();
    p.limb[4] ^= 1u; // perturb y
    EXPECT_FALSE(l2_point_is_valid(p));
    EXPECT_FALSE(l2_ecdh(L2Scalar{{1, 0, 0, 0}}, p).has_value());
}

// A coordinate at or above the field size is not a point. It has to be caught
// here, on the bytes: zisklib's is_on_curve reduces its inputs and would
// answer about a different point.
TEST(L2Ecdh, RejectsNonCanonicalCoordinates)
{
    auto x_over = generator();
    std::memcpy(x_over.limb, SECP256K1_P, sizeof(SECP256K1_P));
    EXPECT_FALSE(l2_point_is_valid(x_over));

    auto y_over = generator();
    std::memcpy(y_over.limb + 4, SECP256K1_P, sizeof(SECP256K1_P));
    EXPECT_FALSE(l2_point_is_valid(y_over));
}

TEST(L2Ecdh, RejectsInvalidScalars)
{
    EXPECT_FALSE(l2_scalar_is_valid(L2Scalar{}));
    L2Scalar n{};
    std::memcpy(n.limb, SECP256K1_N, sizeof(SECP256K1_N));
    EXPECT_FALSE(l2_scalar_is_valid(n));
    L2Scalar n_minus_one = n;
    --n_minus_one.limb[0];
    EXPECT_TRUE(l2_scalar_is_valid(n_minus_one));
    EXPECT_FALSE(l2_ecdh(n, generator()).has_value());
}

TEST(L2Ecdh, ByteRoundTrip)
{
    std::array<unsigned char, 64> be{};
    l2_point_to_be(generator(), std::span<unsigned char, 64>{be});
    EXPECT_EQ(
        l2_point_from_be(std::span<unsigned char const, 64>{be}), generator());

    // Limb 0 is the low 64 bits, so the last byte of the x half is the low
    // byte of limb 0.
    EXPECT_EQ(be[31], static_cast<unsigned char>(generator().limb[0] & 0xFFu));
    EXPECT_EQ(be[0], static_cast<unsigned char>(generator().limb[3] >> 56u));
}
