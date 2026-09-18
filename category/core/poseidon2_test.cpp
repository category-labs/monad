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

// The gate for everything built on Poseidon2. If the host port and the ZisK
// precompile disagree, nothing downstream means anything and the only symptom
// would be a root mismatch with no indication of which side is wrong -- so
// this runs first, and the three vectors are asserted one at a time so a
// failure names which one moved.
//
// The inputs and expected lanes below are restated rather than read out of
// poseidon2.cpp on purpose: the library's copy and this one drifting apart is
// itself a signal, where sharing them would make the test agree with whatever
// the library does.

#include <category/core/poseidon2.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <cstring>

using namespace monad;

namespace
{
    constexpr uint64_t GL_P = 0xFFFFFFFF00000001ULL; // 2^64 - 2^32 + 1

    using State = std::array<uint64_t, 16>;

    // The first four lanes after one permutation, taken from both
    // proofman-fields' native path and the ZisK syscall, which agree.
    void check_vector(State in, std::array<uint64_t, 4> const &want)
    {
        monad_poseidon2_16(in.data());
        for (size_t i = 0; i < want.size(); ++i) {
            EXPECT_EQ(in[i], want[i]) << "lane " << i;
        }
        // Every output lane is a reduced field element. The cipher's squeeze
        // side depends on this: it reads lanes straight out of the state and
        // would otherwise have to reduce them, which is the one place a
        // reduction could go non-injective.
        for (size_t i = 0; i < in.size(); ++i) {
            EXPECT_LT(in[i], GL_P) << "lane " << i << " is not canonical";
        }
    }
}

TEST(Poseidon2, ReferenceVectors)
{
    EXPECT_TRUE(poseidon2_test_vectors());
}

TEST(Poseidon2, AllZeroLanes)
{
    check_vector(
        State{},
        {0xf2b2442ea4d72b98ULL,
         0x08367625af002a12ULL,
         0x41d794a3d56b9451ULL,
         0x533967a2f0a214c8ULL});
}

TEST(Poseidon2, RampLanes)
{
    check_vector(
        State{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15},
        {0x85c54702470d9756ULL,
         0xaa53c7a7d52d9898ULL,
         0x285128096efb0dd7ULL,
         0xf3fde5edd3050ac8ULL});
}

TEST(Poseidon2, LanesJustUnderTheModulus)
{
    check_vector(
        State{
            0xFFFFFFFF00000000ULL,
            1,
            0xFFFFFFFEFFFFFFFFULL,
            2,
            3,
            4,
            5,
            6,
            7,
            8,
            9,
            10,
            11,
            12,
            13,
            0xFFFFFFFF00000000ULL},
        {0x05aff2e318df3719ULL,
         0x4cf20041d8703f9dULL,
         0x4a44a97012a8c804ULL,
         0xbd2adf3afceb6631ULL});
}

// The permutation is not the identity and not a constant map -- a stub that
// returned its input, or zeroed the state, would satisfy neither.
TEST(Poseidon2, DistinctInputsGiveDistinctStates)
{
    State a{};
    State b{};
    b[15] = 1;
    monad_poseidon2_16(a.data());
    monad_poseidon2_16(b.data());
    EXPECT_NE(a, b);
    EXPECT_NE(a, State{});
}

TEST(Poseidon2, SpongeIsDeterministicAndLengthSensitive)
{
    unsigned char const in[3] = {1, 2, 3};
    unsigned char first[32];
    unsigned char again[32];
    unsigned char shorter[32];
    monad_poseidon2_256(in, sizeof(in), first);
    monad_poseidon2_256(in, sizeof(in), again);
    monad_poseidon2_256(in, sizeof(in) - 1, shorter);
    EXPECT_EQ(std::memcmp(first, again, sizeof(first)), 0);
    EXPECT_NE(std::memcmp(first, shorter, sizeof(first)), 0);
}

// Inputs that straddle the sponge's 88-byte rate: the block boundary is where
// an off-by-one in the padding would hide.
TEST(Poseidon2, SpongeAcrossTheRateBoundary)
{
    std::array<unsigned char, 200> in{};
    for (size_t i = 0; i < in.size(); ++i) {
        in[i] = static_cast<unsigned char>(i);
    }
    unsigned char prev[32]{};
    for (size_t len : {0u, 1u, 87u, 88u, 89u, 176u, 177u, 200u}) {
        unsigned char out[32];
        monad_poseidon2_256(in.data(), len, out);
        EXPECT_NE(std::memcmp(out, prev, sizeof(out)), 0) << "len " << len;
        std::memcpy(prev, out, sizeof(prev));
    }
}
