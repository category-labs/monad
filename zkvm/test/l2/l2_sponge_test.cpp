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

// The properties the encryption scheme leans on, not the sponge's internals:
// that separated uses really are separated, that the I/O pattern is committed
// to, and that the rate boundary is where it says it is.
//
// Pattern violations are MONAD_ASSERT, so they abort rather than return -- they
// are programming errors, not inputs. They are covered by death tests, not
// here.

#include <category/core/poseidon2.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <zkvm/guest/l2_sponge.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstdint>
#include <span>
#include <string_view>
#include <vector>

using namespace monad;

namespace
{
    // An arbitrary but fixed label. In production this names the suite and its
    // protocol version; the sponge only hashes it, so any non-empty string
    // exercises the same path -- and LabelSeparates below is what checks that
    // hashing it separates at all.
    constexpr std::string_view LABEL = "test-suite/v1/";

    // Two arbitrary but fixed domain contexts. In production this is the hash
    // of the block-constant half of the cipher's context; here it only has to
    // be 32 bytes.
    std::array<unsigned char, 32> ctx_a()
    {
        std::array<unsigned char, 32> c{};
        for (size_t i = 0; i < c.size(); ++i) {
            c[i] = static_cast<unsigned char>(i + 1);
        }
        return c;
    }

    std::array<unsigned char, 32> ctx_b()
    {
        auto c = ctx_a();
        c[31] ^= 1u;
        return c;
    }

    // Absorb `in`, squeeze `n`, declaring exactly that pattern.
    std::vector<uint64_t>
    run(L2Domain const domain, std::span<uint64_t const> const in,
        size_t const n, std::array<unsigned char, 32> const &context,
        std::string_view const label = LABEL)
    {
        std::array<L2IoOp, 2> const pattern{
            L2IoOp{false, static_cast<uint32_t>(in.size())},
            L2IoOp{true, static_cast<uint32_t>(n)}};
        L2Sponge s{
            domain,
            pattern,
            std::span<unsigned char const, 32>{context},
            label};
        s.absorb(in);
        std::vector<uint64_t> out(n);
        s.squeeze(out);
        s.finish();
        return out;
    }

    std::vector<uint64_t> ramp(size_t const n)
    {
        std::vector<uint64_t> v(n);
        for (size_t i = 0; i < n; ++i) {
            v[i] = i + 1;
        }
        return v;
    }
}

TEST(L2Sponge, Deterministic)
{
    auto const in = ramp(5);
    EXPECT_EQ(
        run(L2Domain::stream, in, 4, ctx_a()),
        run(L2Domain::stream, in, 4, ctx_a()));
}

// The whole point of the domain separator: the same transcript under two uses
// must not let one be read off the other.
TEST(L2Sponge, DomainSeparation)
{
    auto const in = ramp(5);
    auto const kdf = run(L2Domain::kdf, in, 4, ctx_a());
    auto const stream = run(L2Domain::stream, in, 4, ctx_a());
    auto const auth = run(L2Domain::auth, in, 4, ctx_a());
    EXPECT_NE(kdf, stream);
    EXPECT_NE(kdf, auth);
    EXPECT_NE(stream, auth);
}

// The domain context carries the cipher's block-constant fields, so it has to
// separate as hard as the domain itself does. One byte of difference and
// nothing in common -- otherwise moving those fields out of the rate would have
// weakened what binds them.
TEST(L2Sponge, DomainContextSeparates)
{
    auto const in = ramp(5);
    EXPECT_NE(
        run(L2Domain::stream, in, 4, ctx_a()),
        run(L2Domain::stream, in, 4, ctx_b()));
}

// Two suites sharing this permutation are separated by their labels and
// nothing else, so a label that did not reach the tag would leave them one
// oracle. This is the test that makes the required parameter earn its keep.
TEST(L2Sponge, LabelSeparates)
{
    auto const in = ramp(5);
    EXPECT_NE(
        run(L2Domain::stream, in, 4, ctx_a(), "suite-a/v1/"),
        run(L2Domain::stream, in, 4, ctx_a(), "suite-b/v1/"));
}

TEST(L2Sponge, DistinctInputsGiveDistinctOutputs)
{
    auto a = ramp(5);
    auto b = ramp(5);
    b[4] ^= 1u;
    EXPECT_NE(
        run(L2Domain::stream, a, 4, ctx_a()),
        run(L2Domain::stream, b, 4, ctx_a()));
}

// A different declared pattern is a different initial state, even when the
// elements absorbed are a prefix of the same ramp.
TEST(L2Sponge, PatternLengthIsCommittedTo)
{
    EXPECT_NE(
        run(L2Domain::stream, ramp(5), 4, ctx_a()),
        run(L2Domain::stream, ramp(6), 4, ctx_a()));
    auto const in = ramp(5);
    auto const four = run(L2Domain::stream, in, 4, ctx_a());
    auto const five = run(L2Domain::stream, in, 5, ctx_a());
    // The first four squeezed lanes differ too: the tag differs, so the whole
    // run differs -- it is not a prefix relationship.
    EXPECT_NE(four[0], five[0]);
}

// Consecutive calls of the same kind are merged when the pattern is encoded,
// so splitting an absorb must not change anything. That is what makes the
// transcript, rather than the call boundaries, the thing committed to.
TEST(L2Sponge, SplittingACallChangesNothing)
{
    auto const in = ramp(7);

    std::array<L2IoOp, 3> const split{
        L2IoOp{false, 3}, L2IoOp{false, 4}, L2IoOp{true, 4}};
    auto const context = ctx_a();
    L2Sponge a{
        L2Domain::auth,
        split,
        std::span<unsigned char const, 32>{context},
        LABEL};
    a.absorb(std::span{in}.first(3));
    a.absorb(std::span{in}.subspan(3));
    std::array<uint64_t, 4> got_a{};
    a.squeeze(got_a);
    a.finish();

    auto const merged = run(L2Domain::auth, in, 4, ctx_a());
    EXPECT_TRUE(std::equal(got_a.begin(), got_a.end(), merged.begin()));
}

// Rate 12: absorbing 12 then 13 elements must not collide, and squeezing past
// 12 must keep producing -- an off-by-one either way shows up here.
TEST(L2Sponge, RateBoundary)
{
    auto const at = run(L2Domain::stream, ramp(12), 4, ctx_a());
    auto const over = run(L2Domain::stream, ramp(13), 4, ctx_a());
    EXPECT_NE(at, over);

    auto const wide = run(L2Domain::stream, ramp(3), 30, ctx_a());
    ASSERT_EQ(wide.size(), 30u);
    // Distinct lanes across three permutations' worth of output. Not a
    // uniformity claim -- just that the squeeze is not stuck on one lane.
    std::vector<uint64_t> sorted = wide;
    std::sort(sorted.begin(), sorted.end());
    EXPECT_EQ(std::unique(sorted.begin(), sorted.end()), sorted.end());
}

TEST(L2Sponge, SqueezedLanesAreCanonical)
{
    for (uint64_t const lane : run(L2Domain::stream, ramp(3), 24, ctx_a())) {
        EXPECT_LT(lane, GOLDILOCKS_P);
    }
}

TEST(L2PackBytes, SevenBytesPerElementLittleEndian)
{
    std::array<unsigned char, 7> const in{1, 2, 3, 4, 5, 6, 7};
    std::array<uint64_t, 1> out{};
    ASSERT_EQ(l2_pack_bytes(in, out), 1u);
    EXPECT_EQ(out[0], 0x07060504030201ULL);
    EXPECT_LT(out[0], GOLDILOCKS_P);
}

TEST(L2PackBytes, CountIsCeilAndTailIsZeroFilled)
{
    std::array<unsigned char, 9> const in{1, 2, 3, 4, 5, 6, 7, 8, 9};
    std::array<uint64_t, 2> out{};
    ASSERT_EQ(l2_pack_bytes(in, out), 2u);
    EXPECT_EQ(out[0], 0x07060504030201ULL);
    EXPECT_EQ(out[1], 0x0908ULL); // 8 and 9, then zeros
}

TEST(L2PackBytes, EmptyAndCanonical)
{
    std::array<uint64_t, 4> out{};
    EXPECT_EQ(l2_pack_bytes({}, out), 0u);

    std::array<unsigned char, 28> in{};
    for (size_t i = 0; i < in.size(); ++i) {
        in[i] = 0xFF;
    }
    ASSERT_EQ(l2_pack_bytes(in, out), 4u);
    for (uint64_t const e : out) {
        EXPECT_EQ(e, 0x00FFFFFFFFFFFFFFULL);
        EXPECT_LT(e, GOLDILOCKS_P);
    }
}
