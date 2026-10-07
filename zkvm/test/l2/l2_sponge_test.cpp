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

// Test domain separation, I/O-pattern binding and rate boundaries. Pattern
// misuse is a programming error covered by death tests.

#include <category/core/poseidon2.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <zkvm/guest/l2_sponge.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <span>
#include <string>
#include <string_view>
#include <vector>

using namespace monad;

namespace
{
    // Fixed test suite label; LabelSeparates checks that it affects output.
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

// Changing the application context must change the sponge output.
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

// Cached and uncached tags must agree on hits, misses, context/label changes,
// eviction and patterns too large to cache.
TEST(L2Sponge, TagCacheIsTransparent)
{
    L2SpongeTags tags;
    auto const cached = [&tags](
                            L2Domain const domain,
                            std::span<uint64_t const> const in,
                            size_t const n,
                            std::array<unsigned char, 32> const &context,
                            std::string_view const label) {
        std::array<L2IoOp, 2> const pattern{
            L2IoOp{false, static_cast<uint32_t>(in.size())},
            L2IoOp{true, static_cast<uint32_t>(n)}};
        L2Sponge s{
            domain,
            pattern,
            std::span<unsigned char const, 32>{context},
            label,
            tags};
        s.absorb(in);
        std::vector<uint64_t> out(n);
        s.squeeze(out);
        s.finish();
        return out;
    };

    // Twice over, so the second round is served from the cache.
    for (int round = 0; round < 2; ++round) {
        for (L2Domain const d :
             {L2Domain::kdf, L2Domain::stream, L2Domain::auth}) {
            for (size_t const len : {1u, 5u, 12u, 13u, 30u}) {
                EXPECT_EQ(
                    cached(d, ramp(len), 4, ctx_a(), LABEL),
                    run(d, ramp(len), 4, ctx_a()))
                    << "round " << round << " len " << len;
            }
        }
    }

    // Another context, then the first again: each must rebind, not serve the
    // other's tags.
    EXPECT_EQ(
        cached(L2Domain::stream, ramp(5), 4, ctx_b(), LABEL),
        run(L2Domain::stream, ramp(5), 4, ctx_b()));
    EXPECT_EQ(
        cached(L2Domain::stream, ramp(5), 4, ctx_a(), LABEL),
        run(L2Domain::stream, ramp(5), 4, ctx_a()));

    // Another label.
    constexpr std::string_view OTHER = "other-suite/v1/";
    EXPECT_EQ(
        cached(L2Domain::stream, ramp(5), 4, ctx_a(), OTHER),
        run(L2Domain::stream, ramp(5), 4, ctx_a(), OTHER));

    // More distinct patterns than it holds, twice: replacement must never
    // hand one pattern another's tag.
    for (int round = 0; round < 2; ++round) {
        for (size_t len = 1; len <= 20; ++len) {
            EXPECT_EQ(
                cached(L2Domain::auth, ramp(len), 4, ctx_a(), LABEL),
                run(L2Domain::auth, ramp(len), 4, ctx_a()))
                << "round " << round << " len " << len;
        }
    }

    // A pattern merging to six words, past what the cache keeps: served
    // without it, and still the same sponge.
    std::array<L2IoOp, 6> const long_pattern{
        L2IoOp{false, 2},
        L2IoOp{true, 1},
        L2IoOp{false, 2},
        L2IoOp{true, 1},
        L2IoOp{false, 2},
        L2IoOp{true, 3}};
    auto const context = ctx_a();
    auto const in = ramp(6);
    auto const walk = [&](L2Sponge &s) {
        std::vector<uint64_t> out(5);
        s.absorb(std::span{in}.first(2));
        s.squeeze(std::span{out}.first(1));
        s.absorb(std::span{in}.subspan(2, 2));
        s.squeeze(std::span{out}.subspan(1, 1));
        s.absorb(std::span{in}.subspan(4));
        s.squeeze(std::span{out}.subspan(2));
        s.finish();
        return out;
    };
    L2Sponge with_cache{
        L2Domain::kdf,
        long_pattern,
        std::span<unsigned char const, 32>{context},
        LABEL,
        tags};
    L2Sponge without{
        L2Domain::kdf,
        long_pattern,
        std::span<unsigned char const, 32>{context},
        LABEL};
    EXPECT_EQ(walk(with_cache), walk(without));
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

// Known answers pin the function used by existing L2 ciphertexts. Relational
// tests alone cannot detect a consistent but incompatible change. Store short
// outputs directly and fold longer ones.
namespace
{
    // FNV-1a over the lanes, as hex: enough to see any change, and not a hash
    // anything relies on.
    std::string fold(std::span<uint64_t const> const lanes)
    {
        uint64_t h = 0xcbf29ce484222325ULL;
        for (uint64_t const lane : lanes) {
            for (unsigned i = 0; i < 8; ++i) {
                h ^= (lane >> (8 * i)) & 0xff;
                h *= 0x100000001b3ULL;
            }
        }
        char buf[19];
        std::snprintf(
            buf, sizeof(buf), "0x%016llx", static_cast<unsigned long long>(h));
        return buf;
    }
}

TEST(L2Sponge, KnownAnswers)
{
    // One short transcript per domain, the first in full so that a failure
    // names the lane.
    EXPECT_EQ(
        run(L2Domain::kdf, ramp(5), 4, ctx_a()),
        (std::vector<uint64_t>{
            0x8961c69a98b06ae2ULL,
            0x26a7df3e8911ceadULL,
            0x7eb269a51b6bbc79ULL,
            0x199a4638e9c285a3ULL}));
    EXPECT_EQ(
        fold(run(L2Domain::stream, ramp(5), 4, ctx_a())), "0xb4e39c9d63c5eeae");
    EXPECT_EQ(
        fold(run(L2Domain::auth, ramp(5), 4, ctx_a())), "0xd6da11e18dca85f6");

    // Across both rate boundaries: thirteen absorbed, thirty squeezed.
    EXPECT_EQ(
        fold(run(L2Domain::stream, ramp(13), 30, ctx_a())),
        "0x6af26948c6bc820d");

    // Two direction changes, each on a part-filled rate, and an absorb split
    // across calls of different lengths.
    std::array<L2IoOp, 5> const pattern{
        L2IoOp{false, 5},
        L2IoOp{true, 3},
        L2IoOp{false, 9},
        L2IoOp{false, 5},
        L2IoOp{true, 13}};
    auto const context = ctx_b();
    L2Sponge s{
        L2Domain::auth,
        pattern,
        std::span<unsigned char const, 32>{context},
        LABEL};
    auto const in = ramp(19);
    std::vector<uint64_t> out(16);
    s.absorb(std::span{in}.first(5));
    s.squeeze(std::span{out}.first(3));
    s.absorb(std::span{in}.subspan(5, 9));
    s.absorb(std::span{in}.subspan(14));
    s.squeeze(std::span{out}.subspan(3));
    s.finish();
    EXPECT_EQ(fold(out), "0x8a181bd02cdd4be4");
}
