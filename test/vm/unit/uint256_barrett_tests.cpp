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

#include <category/core/assert.h>
#include <category/core/runtime/uint256.hpp>
#include <category/core/runtime/uint256/types.hpp>

#include <intx/intx.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <format>
#include <random>
#include <span>
#include <utility>
#include <vector>

using namespace monad;

namespace
{
    // Fixed seed: failures are reproducible; the seed is printed in the
    // scoped trace of every random case.
    constexpr uint64_t FIXED_SEED = 0xba77e7705eed2026;
    constexpr size_t RANDOM_DENOMINATORS_PER_ALIAS = 6;
    constexpr size_t RANDOM_INPUTS = 12;
    constexpr std::array<size_t, 9> WORD_BOUNDARY_NEIGHBOUR_WIDTHS{
        63, 64, 65, 127, 128, 129, 191, 192, 193};
    constexpr std::array<size_t, 2> UINT256_TOP_WIDTHS{255, 256};

    // Numeric stream tags, one per operation family.
    enum stream_tag : uint64_t
    {
        HELPER_TAG = 1,
        UDIVREM_TAG = 2,
        ADDMOD_TAG = 3,
        MULMOD_TAG = 4,
        MULMOD_CONST_TAG = 5,
        SDIVREM_TAG = 6,
        BIT_SHIFT_TAG = 8,
    };

    // Index reserved for a family's denominator-generation stream, kept
    // separate from its per-denominator input streams.
    constexpr uint64_t DENOMINATOR_STREAM = ~uint64_t{0};

    // The GOLDEN_GAMMA increment from Steele, Lea & Flood (OOPSLA 2014)
    // followed by David Stafford's Mix13 variant of the MurmurHash3 finalizer.
    // Additional sources: JDK 8's SplittableRandom (mix64) and Vigna's
    // splitmix64.c. Used only to derive stream seeds.
    constexpr uint64_t splitmix64(uint64_t z)
    {
        z += 0x9e3779b97f4a7c15;
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9;
        z = (z ^ (z >> 27)) * 0x94d049bb133111eb;
        return z ^ (z >> 31);
    }

    // Independent stream per (tag, index): adding draws in one case does
    // not shift the operands of any other case. The fixed seed and tags are
    // the recorded reproduction identifiers.
    std::mt19937_64 stream(uint64_t const tag, uint64_t const index)
    {
        return std::mt19937_64{
            splitmix64(splitmix64(FIXED_SEED ^ tag) ^ index)};
    }

    // Alias-qualified tag: the denominator interval bit widths distinguish
    // the four interval aliases and the catch-all within a family.
    template <typename Rec>
    constexpr uint64_t alias_tag(uint64_t const op)
    {
        return (op << 32) | (uint64_t{Rec::MIN_DENOMINATOR_BITS} << 16) |
               uint64_t{Rec::MAX_DENOMINATOR_BITS};
    }

    ::intx::uint256 to_intx(uint256_t const &x)
    {
        return ::intx::uint256{x[0], x[1], x[2], x[3]};
    }

    ::intx::uint512 to_intx512(uint256_t const &x)
    {
        return ::intx::uint512{to_intx(x)};
    }

    // Sampling primitives. Preconditions are enforced with MONAD_ASSERT in
    // every build configuration. Bounded choices use rejection on raw
    // mt19937_64 outputs, which is exact and independent of
    // std::uniform_int_distribution, whose algorithm is
    // implementation-defined ([rand.dist.general]/3).

    uint256_t raw_uint256(std::mt19937_64 &rng)
    {
        return uint256_t{rng(), rng(), rng(), rng()};
    }

    // Uniform integer in [0, n). Acceptance exceeds 1/2, so the expected
    // number of draws is below two.
    uint64_t bounded_choice(std::mt19937_64 &rng, uint64_t const n)
    {
        MONAD_ASSERT(n != 0);
        if (n == 1) {
            return 0;
        }
        uint64_t const mask = ~uint64_t{0} >> std::countl_zero(n - 1);
        for (;;) {
            uint64_t const v = rng() & mask;
            if (v < n) {
                return v;
            }
        }
    }

    // Uniform over the low `bits` bits (zero included); higher bits zero.
    uint256_t random_low_bits(std::mt19937_64 &rng, size_t const bits)
    {
        MONAD_ASSERT(bits >= 1 && bits <= uint256_t::num_bits);
        uint256_t r{0};
        for (size_t i = 0; i < (bits + 63) / 64; i++) {
            r[i] = rng();
        }
        size_t const top = bits - 1;
        r[top / 64] &= (~uint64_t{0}) >> (63 - top % 64);
        return r;
    }

    // Uniform value of exact bit width `bits`, i.e. in
    // [2^(bits-1), 2^bits - 1]. Never returns zero.
    uint256_t random_exact_bit_width(std::mt19937_64 &rng, size_t const bits)
    {
        MONAD_ASSERT(bits >= 1 && bits <= uint256_t::num_bits);
        auto r = random_low_bits(rng, bits);
        r[(bits - 1) / 64] |= uint64_t{1} << ((bits - 1) % 64);
        return r;
    }

    // Exact uniform sample from [lo, hi] (inclusive). Termination is
    // probabilistic: acceptance exceeds 1/2 per draw.
    uint256_t uniform_inclusive(
        std::mt19937_64 &rng, uint256_t const &lo, uint256_t const &hi)
    {
        MONAD_ASSERT(lo <= hi);
        uint256_t const width = hi - lo;
        if (width == 0) {
            return lo;
        }
        if (width == ~uint256_t{0}) {
            return raw_uint256(rng);
        }
        for (;;) {
            auto const offset = random_low_bits(rng, bit_width(width));
            if (offset <= width) {
                return lo + offset;
            }
        }
    }

    // Bit-width-uniform sample from [lo, hi]: pick an occupied binary magnitude
    // band uniformly, then sample uniformly within the band clipped to the
    // interval.  Band 0 is {0} and is occupied only when lo == 0; band w >= 1
    // is [2^(w-1), 2^w - 1], with the w == 256 upper end handled explicitly.
    uint256_t bit_width_uniform_inclusive(
        std::mt19937_64 &rng, uint256_t const &lo, uint256_t const &hi)
    {
        MONAD_ASSERT(lo <= hi);
        size_t const w_lo = bit_width(lo); // 0 iff lo == 0
        size_t const w_hi = bit_width(hi);
        size_t const w =
            w_lo + bounded_choice(rng, static_cast<uint64_t>(w_hi - w_lo) + 1);
        if (w == 0) {
            return 0;
        }
        auto const band_lo = uint256_t{1} << (w - 1);
        auto const band_hi =
            w == uint256_t::num_bits ? ~uint256_t{0} : (uint256_t{1} << w) - 1;
        auto const clip_lo = lo < band_lo ? band_lo : lo;
        auto const clip_hi = hi < band_hi ? hi : band_hi;
        if (clip_lo == band_lo && clip_hi == band_hi) {
            // Unclipped band: an exact-width sample, no rejection needed.
            return random_exact_bit_width(rng, w);
        }
        return uniform_inclusive(rng, clip_lo, clip_hi);
    }

    // Full-range operand: bit-width-uniform over [0, 2^256 - 1].
    uint256_t random_operand(std::mt19937_64 &rng)
    {
        return bit_width_uniform_inclusive(rng, 0, ~uint256_t{0});
    }

    uint256_t min_exact_width_value(size_t const width)
    {
        MONAD_ASSERT(width >= 1 && width <= uint256_t::num_bits);
        return uint256_t{1} << (width - 1);
    }

    uint256_t max_exact_width_value(size_t const width)
    {
        MONAD_ASSERT(width >= 1 && width <= uint256_t::num_bits);
        return width == uint256_t::num_bits ? ~uint256_t{0}
                                            : (uint256_t{1} << width) - 1;
    }

    template <size_t N>
    void append_exact_width_extremes(
        std::vector<uint256_t> &values, std::array<size_t, N> const &widths)
    {
        for (auto const width : widths) {
            values.push_back(min_exact_width_value(width));
            values.push_back(max_exact_width_value(width));
        }
    }

    template <size_t N>
    void append_exact_width_extreme_pairs(
        std::vector<std::pair<uint256_t, uint256_t>> &cases,
        std::array<size_t, N> const &widths)
    {
        for (auto const width : widths) {
            auto const sparse = min_exact_width_value(width);
            auto const dense = max_exact_width_value(width);
            cases.push_back({sparse, sparse});
            cases.push_back({sparse, dense});
            cases.push_back({dense, dense});
        }
    }

    // Denominators for an alias interval: both endpoints, their
    // neighbours, all 2^k - 1 / 2^k / 2^k + 1 within the interval, and a
    // fixed-seed bit-width-uniform sample.
    std::vector<uint256_t> interval_denominators(
        std::mt19937_64 &rng, uint256_t const &min_d, uint256_t const &max_d)
    {
        std::vector<uint256_t> ds;
        auto push = [&](uint256_t const &d) {
            if (min_d <= d && d <= max_d && !std::ranges::contains(ds, d)) {
                ds.push_back(d);
            }
        };
        push(min_d);
        push(min_d + 1);
        push(max_d - 1);
        push(max_d);
        // Retain the exact-width operand extrema p - 1 and p, but include the
        // nearest non-power above each selected bit-width boundary p + 1; it
        // can produce dense reciprocal regions absent from those extrema.
        for (auto const k :
             {1, 2, 63, 64, 65, 127, 128, 129, 191, 192, 193, 254, 255}) {
            auto const p = uint256_t{1} << k;
            push(p - 1);
            push(p);
            push(p + 1);
        }
        for (size_t i = 0; i < RANDOM_DENOMINATORS_PER_ALIAS; i++) {
            push(bit_width_uniform_inclusive(rng, min_d, max_d));
        }
        return ds;
    }

    void push_quotient_remainder_classes(
        std::vector<uint256_t> &xs, std::mt19937_64 &rng, uint256_t const &d)
    {
        auto const d_512 = to_intx512(d);
        auto const max_512 = to_intx512(~uint256_t{0});
        std::array<::intx::uint512, 4> const q_classes{
            0, 1, ::intx::uint512{1} << 64, max_512 / d_512};
        std::array<::intx::uint512, 4> const r_classes{
            0, 1, d_512 - 1, to_intx512(uniform_inclusive(rng, 0, d - 1))};
        for (auto const &q : q_classes) {
            for (auto const &r : r_classes) {
                if (r >= d_512) {
                    continue;
                }
                auto const x_512 = q * d_512 + r;
                if (x_512 > max_512) {
                    continue;
                }
                uint256_t const x{x_512[0], x_512[1], x_512[2], x_512[3]};
                if (!std::ranges::contains(xs, x)) {
                    xs.push_back(x);
                }
            }
        }
    }

    // Inputs for a given denominator: boundary relations to d, the
    // extremes, quotient/remainder classes, and a fixed-seed
    // bit-width-uniform sample.
    std::vector<uint256_t>
    inputs_for_denominator(std::mt19937_64 &rng, uint256_t const &d)
    {
        std::vector<uint256_t> xs{
            0, 1, d - 1, d, d + 1, ~uint256_t{0}, ~uint256_t{0} - 1};
        push_quotient_remainder_classes(xs, rng, d);
        for (size_t i = 0; i < RANDOM_INPUTS; i++) {
            xs.push_back(random_operand(rng));
        }
        return xs;
    }

    template <typename Rec>
    void test_udivrem_alias()
    {
        constexpr uint64_t TAG = alias_tag<Rec>(UDIVREM_TAG);
        auto denom_rng = stream(TAG, DENOMINATOR_STREAM);
        auto const ds = interval_denominators(
            denom_rng, Rec::MIN_DENOMINATOR, Rec::MAX_DENOMINATOR);
        for (size_t di = 0; di < ds.size(); di++) {
            auto const &d = ds[di];
            auto rng = stream(TAG, di);
            Rec const rec(d);
            for (auto const &x : inputs_for_denominator(rng, d)) {
                SCOPED_TRACE(
                    std::format("seed={:#x} x={} d={}", FIXED_SEED, x, d));
                auto const [q, r] = barrett::udivrem(x, rec);
                auto const expect = ::intx::udivrem(to_intx(x), to_intx(d));
                EXPECT_EQ(to_intx(q), expect.quot);
                EXPECT_EQ(to_intx(r), expect.rem);
                EXPECT_TRUE(r < d);
                EXPECT_EQ(
                    to_intx512(q) * to_intx512(d) + to_intx512(r),
                    to_intx512(x));
            }
        }
    }

    template <typename Rec>
    void test_addmod_alias()
    {
        constexpr uint64_t TAG = alias_tag<Rec>(ADDMOD_TAG);
        auto denom_rng = stream(TAG, DENOMINATOR_STREAM);
        auto const ds = interval_denominators(
            denom_rng, Rec::MIN_DENOMINATOR, Rec::MAX_DENOMINATOR);
        for (size_t di = 0; di < ds.size(); di++) {
            auto const &d = ds[di];
            auto rng = stream(TAG, di);
            Rec const rec(d);
            auto const ones = ~uint256_t{0};
            std::vector<std::pair<uint256_t, uint256_t>> cases{
                {ones, uint256_t{1}},
                {d - 1, d - 1},
                {uint256_t{0}, uint256_t{0}},
                {uint256_t{0}, ones},
                {d, d},
                {d - 1, uint256_t{1}},
            };
            append_exact_width_extreme_pairs(
                cases, WORD_BOUNDARY_NEIGHBOUR_WIDTHS);
            append_exact_width_extreme_pairs(cases, UINT256_TOP_WIDTHS);
            for (size_t i = 0; i < RANDOM_INPUTS; i++) {
                cases.push_back({random_operand(rng), random_operand(rng)});
            }
            for (auto const &[x, y] : cases) {
                SCOPED_TRACE(std::format(
                    "seed={:#x} x={} y={} d={}", FIXED_SEED, x, y, d));
                auto const got = barrett::addmod(x, y, rec);
                auto const expect =
                    ::intx::addmod(to_intx(x), to_intx(y), to_intx(d));
                EXPECT_EQ(to_intx(got), expect);
                EXPECT_TRUE(got < d);
            }
        }
    }

    template <typename Rec>
    void test_mulmod_alias()
    {
        constexpr uint64_t TAG = alias_tag<Rec>(MULMOD_TAG);
        auto denom_rng = stream(TAG, DENOMINATOR_STREAM);
        auto const ds = interval_denominators(
            denom_rng, Rec::MIN_DENOMINATOR, Rec::MAX_DENOMINATOR);
        for (size_t di = 0; di < ds.size(); di++) {
            auto const &d = ds[di];
            auto rng = stream(TAG, di);
            Rec const rec(d);
            auto const ones = ~uint256_t{0};
            std::vector<std::pair<uint256_t, uint256_t>> cases{
                {uint256_t{0}, ones},
                {uint256_t{1}, ones},
                {d - 1, d - 1},
            };
            append_exact_width_extreme_pairs(
                cases, WORD_BOUNDARY_NEIGHBOUR_WIDTHS);
            append_exact_width_extreme_pairs(cases, UINT256_TOP_WIDTHS);
            for (size_t i = 0; i < RANDOM_INPUTS; i++) {
                cases.push_back({random_operand(rng), random_operand(rng)});
            }
            for (auto const &[x, y] : cases) {
                SCOPED_TRACE(std::format(
                    "seed={:#x} x={} y={} d={}", FIXED_SEED, x, y, d));
                auto const got = barrett::mulmod(x, y, rec);
                auto const expect =
                    ::intx::mulmod(to_intx(x), to_intx(y), to_intx(d));
                EXPECT_EQ(to_intx(got), expect);
                EXPECT_TRUE(got < d);
            }
        }
    }

    template <typename Rec>
    void test_mulmod_const_alias()
    {
        constexpr uint64_t TAG = alias_tag<Rec>(MULMOD_CONST_TAG);
        auto denom_rng = stream(TAG, DENOMINATOR_STREAM);
        auto const ds = interval_denominators(
            denom_rng, Rec::MIN_DENOMINATOR, Rec::MAX_DENOMINATOR);
        for (size_t di = 0; di < ds.size(); di++) {
            auto const &d = ds[di];
            auto rng = stream(TAG, di);
            std::vector<uint256_t> multipliers{
                0, 1, d - 1, random_operand(rng)};
            append_exact_width_extremes(
                multipliers, WORD_BOUNDARY_NEIGHBOUR_WIDTHS);
            append_exact_width_extremes(multipliers, UINT256_TOP_WIDTHS);
            for (auto const &y : multipliers) {
                Rec const rec(y, d);
                std::vector<uint256_t> xs{0, 1, d - 1, d, d + 1, ~uint256_t{0}};
                for (size_t i = 0; i < RANDOM_INPUTS; i++) {
                    xs.push_back(random_operand(rng));
                }
                for (auto const &x : xs) {
                    SCOPED_TRACE(std::format(
                        "seed={:#x} x={} y={} d={}", FIXED_SEED, x, y, d));
                    auto const got = barrett::mulmod_const(x, rec);
                    auto const expect =
                        ::intx::mulmod(to_intx(x), to_intx(y), to_intx(d));
                    EXPECT_EQ(to_intx(got), expect);
                    EXPECT_TRUE(got < d);
                }
            }
        }
    }
}

// * Sampling helper contracts
//
// Fixed-seed containment and exact-width smoke checks. These assertions
// exercise the range contracts and representative boundary widths.

TEST(uint256_barrett, sampling_helper_contracts)
{
    auto rng = stream(HELPER_TAG, 0);
    constexpr size_t DRAWS = 64;

    // bounded_choice: containment, and the singleton domain is constant.
    for (size_t i = 0; i < DRAWS; i++) {
        EXPECT_EQ(bounded_choice(rng, 1), 0u);
        EXPECT_LT(bounded_choice(rng, 2), 2u);
        EXPECT_LT(bounded_choice(rng, 3), 3u);
        EXPECT_LT(bounded_choice(rng, uint64_t{1} << 63), uint64_t{1} << 63);
        EXPECT_LT(bounded_choice(rng, ~uint64_t{0}), ~uint64_t{0});
    }

    // random_low_bits: value fits in `bits`; random_exact_bit_width: the
    // width is exact, including at word boundaries and both extremes.
    auto const check_width = [&](size_t const bits) {
        for (size_t i = 0; i < DRAWS / 8; i++) {
            EXPECT_LE(bit_width(random_low_bits(rng, bits).as_words()), bits);
            EXPECT_EQ(
                bit_width(random_exact_bit_width(rng, bits).as_words()), bits);
        }
    };
    check_width(size_t{1});
    check_width(size_t{2});
    for (auto const bits : WORD_BOUNDARY_NEIGHBOUR_WIDTHS) {
        check_width(bits);
    }
    for (auto const bits : UINT256_TOP_WIDTHS) {
        check_width(bits);
    }

    auto const ones = ~uint256_t{0};
    auto const in = [](uint256_t const &v,
                       uint256_t const &lo,
                       uint256_t const &hi) { return lo <= v && v <= hi; };

    for (size_t i = 0; i < DRAWS; i++) {
        // Singleton range is constant.
        EXPECT_EQ(uniform_inclusive(rng, 42, 42), 42);
        EXPECT_EQ(bit_width_uniform_inclusive(rng, 42, 42), 42);

        // Full range: any four-word value is in range by construction;
        // exercises the width == 2^256 - 1 special case.
        (void)uniform_inclusive(rng, 0, ones);
        (void)bit_width_uniform_inclusive(rng, 0, ones);

        // Zero-inclusive small range: containment covers band 0.
        EXPECT_LE(uniform_inclusive(rng, 0, 1), 1);
        EXPECT_LE(bit_width_uniform_inclusive(rng, 0, 1), 1);

        // Power-of-two span (offset always accepted, no rejection).
        auto const p_lo = uint256_t{1} << 100;
        auto const p_hi = p_lo + ((uint256_t{1} << 64) - 1);
        EXPECT_TRUE(in(uniform_inclusive(rng, p_lo, p_hi), p_lo, p_hi));

        // Non-power-of-two span crossing a word boundary.
        auto const n_lo = (uint256_t{1} << 64) - 3;
        auto const n_hi = (uint256_t{1} << 64) + 5;
        EXPECT_TRUE(in(uniform_inclusive(rng, n_lo, n_hi), n_lo, n_hi));
        EXPECT_TRUE(
            in(bit_width_uniform_inclusive(rng, n_lo, n_hi), n_lo, n_hi));

        // Skew interval occupying the top of one band: the clipped-band
        // path terminates without rejection-loop pathology.
        auto const s_lo = (uint256_t{1} << 64) - 2;
        auto const s_hi = (uint256_t{1} << 64) - 1;
        EXPECT_TRUE(
            in(bit_width_uniform_inclusive(rng, s_lo, s_hi), s_lo, s_hi));

        // Interval endpoints at the type extremes.
        EXPECT_TRUE(in(
            bit_width_uniform_inclusive(rng, ones - 7, ones), ones - 7, ones));
    }
}

// * udivrem with quotient: every interval alias plus the catch-all

TEST(uint256_barrett, udivrem_1_65)
{
    test_udivrem_alias<barrett::udivrem_reciprocal_1_65>();
}

TEST(uint256_barrett, udivrem_65_129)
{
    test_udivrem_alias<barrett::udivrem_reciprocal_65_129>();
}

TEST(uint256_barrett, udivrem_129_193)
{
    test_udivrem_alias<barrett::udivrem_reciprocal_129_193>();
}

TEST(uint256_barrett, udivrem_193_256)
{
    test_udivrem_alias<barrett::udivrem_reciprocal_193_256>();
}

TEST(uint256_barrett, udivrem_catch_all)
{
    test_udivrem_alias<barrett::udivrem_reciprocal>();
}

// * addmod remainder-only path (257-bit inputs, carry word)

TEST(uint256_barrett, addmod_1_65)
{
    test_addmod_alias<barrett::addmod_reciprocal_1_65>();
}

TEST(uint256_barrett, addmod_65_129)
{
    test_addmod_alias<barrett::addmod_reciprocal_65_129>();
}

TEST(uint256_barrett, addmod_129_193)
{
    test_addmod_alias<barrett::addmod_reciprocal_129_193>();
}

TEST(uint256_barrett, addmod_193_256)
{
    test_addmod_alias<barrett::addmod_reciprocal_193_256>();
}

TEST(uint256_barrett, addmod_catch_all)
{
    test_addmod_alias<barrett::addmod_reciprocal>();
}

// * mulmod remainder-only path (full 512-bit products)

TEST(uint256_barrett, mulmod_1_65)
{
    test_mulmod_alias<barrett::mulmod_reciprocal_1_65>();
}

TEST(uint256_barrett, mulmod_65_129)
{
    test_mulmod_alias<barrett::mulmod_reciprocal_65_129>();
}

TEST(uint256_barrett, mulmod_129_193)
{
    test_mulmod_alias<barrett::mulmod_reciprocal_129_193>();
}

TEST(uint256_barrett, mulmod_193_256)
{
    test_mulmod_alias<barrett::mulmod_reciprocal_193_256>();
}

TEST(uint256_barrett, mulmod_catch_all)
{
    test_mulmod_alias<barrett::mulmod_reciprocal>();
}

// * Correction-count witnesses
//
// The reduce soundness comment in category/core/runtime/uint256.hpp proves
// q - 2 <= q_hat <= q when a pre-product shift is applied; measured
// coverage showed the fixed corpus never reached the two-correction exit.
// The witnesses below pin it deterministically for every exported interval
// where a two-correction estimate is reachable.

namespace
{
    template <size_t N>
    void expect_retained_estimate_two_below(
        words_t<N> const &q_hat, ::intx::uint512 const &quotient)
    {
        static_assert(0 < N && N <= ::intx::uint512::num_words);
        // Remainder-only estimates retain just the quotient words that can
        // affect r_hat, so compare every retained word against q - 2.
        auto const q_minus_2 = quotient - 2;
        for (size_t w = 0; w < N; w++) {
            EXPECT_EQ(q_hat[w], q_minus_2[w]) << "quotient word " << w;
        }
    }

    template <typename Rec>
    void
    check_udivrem_two_correction_witness(uint256_t const &d, uint256_t const &x)
    {
        Rec const rec(d);
        auto const expect = ::intx::udivrem(to_intx(x), to_intx(d));

        auto const q_hat = rec.template estimate_q<true>(x.as_words());
        expect_retained_estimate_two_below(q_hat, expect.quot);

        auto const [q, r] = barrett::udivrem(x, rec);
        EXPECT_EQ(to_intx(q), expect.quot);
        EXPECT_EQ(to_intx(r), expect.rem);
    }

    template <typename Rec>
    void check_addmod_two_correction_witness(
        uint256_t const &d, uint256_t const &x, uint256_t const &y)
    {
        Rec const rec(d);

        auto const [sum_base, carry] = addc(x, y);
        EXPECT_TRUE(carry);
        words_t<5> const sum{
            sum_base[0],
            sum_base[1],
            sum_base[2],
            sum_base[3],
            static_cast<uint64_t>(carry)};
        auto const sum_512 =
            to_intx512(sum_base) +
            (::intx::uint512{static_cast<uint64_t>(carry)} << 256);
        auto const quotient = sum_512 / to_intx512(d);

        auto const q_hat = rec.template estimate_q<false>(sum);
        expect_retained_estimate_two_below(q_hat, quotient);

        EXPECT_EQ(
            to_intx(barrett::addmod(x, y, rec)),
            ::intx::addmod(to_intx(x), to_intx(y), to_intx(d)));
    }

    template <typename Rec>
    void check_mulmod_two_correction_witness(
        uint256_t const &d, uint256_t const &x, uint256_t const &y,
        uint256_t const &expected_remainder)
    {
        Rec const rec(d);
        auto const product = to_intx512(x) * to_intx512(y);
        auto const quotient = product / to_intx512(d);

        words_t<8> product_words;
        for (size_t w = 0; w < product_words.size(); w++) {
            product_words[w] = product[w];
        }
        auto const q_hat = rec.template estimate_q<false>(product_words);
        expect_retained_estimate_two_below(q_hat, quotient);

        auto const got = barrett::mulmod(x, y, rec);
        EXPECT_EQ(
            to_intx(got), ::intx::mulmod(to_intx(x), to_intx(y), to_intx(d)));
        EXPECT_EQ(got, expected_remainder);
    }

    // d = 2^65 + 1, shared by the three 65_129 witnesses.
    uint256_t const witness_d_65_129{1, 2, 0, 0};
}

TEST(uint256_barrett, udivrem_65_129_two_correction_witness)
{
    check_udivrem_two_correction_witness<barrett::udivrem_reciprocal_65_129>(
        witness_d_65_129,
        0xf646e1f41412f92f530c49cd0462db9d49ca042dcafd9a2eeeeacbe226e87556_u256);
}

TEST(uint256_barrett, udivrem_129_193_two_correction_witness)
{
    check_udivrem_two_correction_witness<barrett::udivrem_reciprocal_129_193>(
        0x200000000000000000000000000000005_u256,
        0xc55920a6d3746bc2d68327e053db3b2fed5ed1a110a30d671847e3b0d1a413f3_u256);
}

TEST(uint256_barrett, udivrem_193_256_two_correction_witness)
{
    check_udivrem_two_correction_witness<barrett::udivrem_reciprocal_193_256>(
        0x2301e56063798b0f18c709c68ac90dace18dc4786cdf4ffb9_u256,
        0xfffffffffffffff7e48579b3a55809312b5aefa65a25922024220b032017e622_u256);
}

TEST(uint256_barrett, addmod_65_129_two_correction_witness)
{
    check_addmod_two_correction_witness<barrett::addmod_reciprocal_65_129>(
        witness_d_65_129,
        ~uint256_t{0},
        0x732edc2269b2817e0fd7265cb2a73e9608cecd497e75b99daed77891dfc75d5a_u256);
}

TEST(uint256_barrett, addmod_129_193_two_correction_witness)
{
    check_addmod_two_correction_witness<barrett::addmod_reciprocal_129_193>(
        0x200000000000000000000000000000003_u256,
        ~uint256_t{0},
        0x2c40307e26fc61880ef8337cd451fad5c26048bd3a7a924c16744d3b3e7af83f_u256);
}

TEST(uint256_barrett, addmod_193_256_two_correction_witness)
{
    check_addmod_two_correction_witness<barrett::addmod_reciprocal_193_256>(
        0x2061fe10104d6a61115b0f770232bedcb6225ee20400c10c9_u256,
        ~uint256_t{0},
        0xffffffffffffffcdff9826286e610fffc8a18ea502f4586490a9702bb65ffd03_u256);
}

TEST(uint256_barrett, mulmod_65_129_two_correction_witness)
{
    check_mulmod_two_correction_witness<barrett::mulmod_reciprocal_65_129>(
        witness_d_65_129,
        0xfc44ae05c246267143eb839d8ea6e71e0643551496d19b09b89e5e4361fe0322_u256,
        0xf4a32e6b31115e6cd4e145833f23cfea5a175be4f05c18696ab723a7ccbaf169_u256,
        uint256_t{0xacbccdd8281637bd});
}

TEST(uint256_barrett, mulmod_129_193_two_correction_witness)
{
    check_mulmod_two_correction_witness<barrett::mulmod_reciprocal_129_193>(
        0x200000000000000000000000000000001_u256,
        0xd89f6e3cb44ae6cb45d92595b0cdc9618c833bf96de69edf2df4258ee388d74f_u256,
        0xdbdb4ecee1f9ff55f188ec80a4b49d0497ee234ae04783fd6adcbe4b6db9b7e2_u256,
        0x8a7e7d18763db6d6fe61333c27fb0cf_u256);
}

TEST(uint256_barrett, mulmod_193_256_two_correction_witness)
{
    check_mulmod_two_correction_witness<barrett::mulmod_reciprocal_193_256>(
        0x22e4253c0c407f4abc95938c5ca1e204338c8145dab7e33dd_u256,
        0xea2f57add0e22facbf12eb95f2a4991c6a129cbb8c627b8c19d14cc872901546_u256,
        0xed669f4d2941558f861d60be7cc09cc80df69d491f958ad18aeac18bf4178454_u256,
        0x639351fb2067516b7f1efcc70e66c9090af3bad972059e59_u256);
}

// * mulmod_const (constant multiplier baked into the reciprocal)

TEST(uint256_barrett, mulmod_const_1_65)
{
    test_mulmod_const_alias<barrett::mulmod_const_reciprocal_1_65>();
}

TEST(uint256_barrett, mulmod_const_65_129)
{
    test_mulmod_const_alias<barrett::mulmod_const_reciprocal_65_129>();
}

TEST(uint256_barrett, mulmod_const_129_193)
{
    test_mulmod_const_alias<barrett::mulmod_const_reciprocal_129_193>();
}

TEST(uint256_barrett, mulmod_const_193_256)
{
    test_mulmod_const_alias<barrett::mulmod_const_reciprocal_193_256>();
}

TEST(uint256_barrett, mulmod_const_catch_all)
{
    test_mulmod_const_alias<barrett::mulmod_const_reciprocal>();
}

namespace
{
    template <typename Rec>
    void check_sdivrem(
        Rec const &rec, uint256_t const &x, uint256_t const &d_abs,
        bool const d_neg)
    {
        SCOPED_TRACE(std::format("x={} |d|={} d_neg={}", x, d_abs, d_neg));
        auto const [q, r] = barrett::sdivrem(x, d_neg, rec);
        auto const d_signed = d_neg ? -d_abs : d_abs;
        auto const expect = ::intx::sdivrem(to_intx(x), to_intx(d_signed));
        EXPECT_EQ(to_intx(q), expect.quot);
        EXPECT_EQ(to_intx(r), expect.rem);
        // Magnitude and sign invariants (Yellow Paper SMOD): |r| < |d|,
        // and a nonzero remainder has the numerator's sign.
        auto const r_abs = (r[3] >> 63) ? -r : r;
        EXPECT_TRUE(r_abs < d_abs);
        if (r != 0) {
            EXPECT_EQ(r[3] >> 63, x[3] >> 63);
        }
    }

    // All distinct representable sign combinations for each magnitude pair.
    // Negative zero is skipped, and denominator magnitude 2^255 is available
    // only as -2^255. The INT_MIN numerator is covered separately.
    template <typename Rec>
    void check_sdivrem_signs(
        Rec const &rec, uint256_t const &x_abs, uint256_t const &d_abs)
    {
        for (bool const x_neg : {false, true}) {
            if (x_neg && x_abs == 0) {
                continue;
            }
            for (bool const d_neg : {false, true}) {
                // Magnitude 2^255 is representable only as the negative
                // value -2^255; +2^255 is not a signed 256-bit value.
                if (!d_neg && d_abs == uint256_t{1} << 255) {
                    continue;
                }
                check_sdivrem(rec, x_neg ? -x_abs : x_abs, d_abs, d_neg);
            }
        }
    }

    std::vector<uint256_t> signed_magnitudes_for_denominator(
        std::mt19937_64 &rng, uint256_t const &d_abs)
    {
        auto const int_max = (uint256_t{1} << 255) - 1;
        std::vector<uint256_t> xs;
        auto push = [&](uint256_t const &x) {
            if (x <= int_max && !std::ranges::contains(xs, x)) {
                xs.push_back(x);
            }
        };

        push(0);
        push(1);
        push(d_abs - 1);
        push(d_abs);
        push(d_abs + 1);
        push(int_max);
        for (size_t i = 0; i < RANDOM_INPUTS; i++) {
            push(bit_width_uniform_inclusive(rng, 0, int_max));
        }
        return xs;
    }

    template <typename Rec>
    void test_sdivrem_alias()
    {
        constexpr uint64_t TAG = alias_tag<Rec>(SDIVREM_TAG);
        auto const int_min = uint256_t{1} << 255;

        // Denominator magnitudes are clamped to 2^255: larger unsigned
        // values are not magnitudes of any signed 256-bit denominator.
        auto const d_hi = std::min(Rec::MAX_DENOMINATOR, int_min);

        auto denom_rng = stream(TAG, DENOMINATOR_STREAM);
        auto const ds =
            interval_denominators(denom_rng, Rec::MIN_DENOMINATOR, d_hi);

        for (size_t di = 0; di < ds.size(); di++) {
            auto const &d_abs = ds[di];
            auto rng = stream(TAG, di);
            Rec const rec(d_abs);

            // Zero numerator, units, exact division (x_abs == d_abs),
            // |x| < |d|, neighbours of d, INT_MAX, and generated
            // magnitudes, de-duplicated within the signed range.
            for (auto const &x_abs :
                 signed_magnitudes_for_denominator(rng, d_abs)) {
                check_sdivrem_signs(rec, x_abs, d_abs);
            }

            // The INT_MIN bit pattern with both denominator signs (the
            // positive sign only when the magnitude is representable).
            if (d_abs != int_min) {
                check_sdivrem(rec, int_min, d_abs, false);
            }
            check_sdivrem(rec, int_min, d_abs, true);
        }
    }
}

TEST(uint256_barrett, sdivrem_1_65)
{
    test_sdivrem_alias<barrett::udivrem_reciprocal_1_65>();
}

TEST(uint256_barrett, sdivrem_65_129)
{
    test_sdivrem_alias<barrett::udivrem_reciprocal_65_129>();
}

TEST(uint256_barrett, sdivrem_129_193)
{
    test_sdivrem_alias<barrett::udivrem_reciprocal_129_193>();
}

TEST(uint256_barrett, sdivrem_193_256)
{
    test_sdivrem_alias<barrett::udivrem_reciprocal_193_256>();
}

// * Non-exported generic-surface tests

namespace
{
    // Non-exported reciprocal with denominator interval starting at 1, so
    // that d == 1 (excluded from the exported aliases) is also covered.
    using full_range_udivrem_reciprocal = barrett::reciprocal<{
        .min_denominator = uint256_t{1}.as_words(),
        .max_denominator = (~uint256_t{0}).as_words(),
        .input_bits = 256}>;

    // Non-exported constant-multiplier reciprocal (SHIFT % 64 == 1).
    using bit_shift_mulmod_const_reciprocal = barrett::reciprocal<{
        .min_denominator = (uint256_t{1} << 1).as_words(),
        .max_denominator = ((uint256_t{1} << 65) - 1).as_words(),
        .input_bits = 257,
        .multiplier_bits = 256}>;
    static_assert(bit_shift_mulmod_const_reciprocal::BIT_SHIFT == 1);
}

TEST(uint256_barrett, full_range_reciprocal_division_by_one)
{
    full_range_udivrem_reciprocal const rec(uint256_t{1});
    std::vector<uint256_t> xs{0, 1, ~uint256_t{0}, uint256_t{1} << 255};
    for (auto const &x : xs) {
        SCOPED_TRACE(std::format("x={}", x));
        auto const [q, r] = barrett::udivrem(x, rec);
        EXPECT_EQ(q, x);
        EXPECT_EQ(r, 0);
    }

    // This API operates on unsigned two's-complement bit patterns and
    // intentionally implements the EVM wrap result defined by the Yellow
    // Paper (SDIV(-2^255, -1) = -2^255); it does not perform C++ signed
    // division, for which this case would be undefined behavior.
    auto const minus_one = ~uint256_t{0};
    for (auto const &x : xs) {
        SCOPED_TRACE(std::format("x={}", x));
        auto const [q, r] = barrett::sdivrem(x, true, rec);
        auto const expect = ::intx::sdivrem(to_intx(x), to_intx(minus_one));
        EXPECT_EQ(to_intx(q), expect.quot);
        EXPECT_EQ(to_intx(r), expect.rem);
    }
}

TEST(uint256_barrett, nonzero_bit_shift_multiplier_numerator)
{
    using rec_t = bit_shift_mulmod_const_reciprocal;

    // Verifies the constructor against floor((y << 257) / d) word-for-word
    // and reduce<true> on a 257-bit input against a 576-bit oracle. The
    // quotient output span keeps the low four words, so the quotient check
    // is equality modulo 2^256; the remainder check is exact.
    auto const check = [](uint256_t const &y,
                          uint256_t const &d,
                          words_t<5> const &x) {
        SCOPED_TRACE(
            std::format("y={} d={} x4={:#x} x3={:#x}", y, d, x[4], x[3]));
        rec_t const rec(y, d);

        using oracle_t = ::intx::uint<576>;
        auto const y_oracle = oracle_t{to_intx(y)};
        auto const d_oracle = oracle_t{to_intx(d)};
        auto const expect_rec = (y_oracle << 257) / d_oracle;
        for (size_t w = 0; w < rec_t::RECIPROCAL_WORDS; w++) {
            EXPECT_EQ(rec.reciprocal_[w], expect_rec[w])
                << "reciprocal word " << w;
        }

        oracle_t const x_oracle{x[0], x[1], x[2], x[3], x[4]};

        div_result<uint256_t> result{.quot = {0}, .rem = {0}};
        rec.reduce<true>(
            x,
            std::span<uint64_t, uint256_t::num_words>(result.quot.as_words()),
            std::span<uint64_t, uint256_t::num_words>(result.rem.as_words()));

        auto const expect = ::intx::udivrem(x_oracle * y_oracle, d_oracle);
        EXPECT_EQ(oracle_t{to_intx(result.rem)}, expect.rem);
        for (size_t w = 0; w < uint256_t::num_words; w++) {
            EXPECT_EQ(result.quot[w], expect.quot[w]) << "quotient word " << w;
        }
    };

    auto denom_rng = stream(BIT_SHIFT_TAG, DENOMINATOR_STREAM);
    auto const ds = interval_denominators(
        denom_rng, rec_t::MIN_DENOMINATOR, rec_t::MAX_DENOMINATOR);

    std::vector<uint256_t> ys{0, 1};
    append_exact_width_extremes(ys, WORD_BOUNDARY_NEIGHBOUR_WIDTHS);
    append_exact_width_extremes(ys, UINT256_TOP_WIDTHS);
    words_t<5> const x_max{
        ~uint64_t{0}, ~uint64_t{0}, ~uint64_t{0}, ~uint64_t{0}, 1};
    words_t<5> const x_zero{0, 0, 0, 0, 0};
    for (size_t di = 0; di < ds.size(); di++) {
        auto const &d = ds[di];
        for (auto const &y : ys) {
            check(y, d, x_max);
            check(y, d, x_zero);
        }

        auto rng = stream(BIT_SHIFT_TAG, di);
        auto const y = random_operand(rng);
        auto const x_lo = random_operand(rng);
        words_t<5> const x{x_lo[0], x_lo[1], x_lo[2], x_lo[3], rng() & 1};
        check(y, d, x);
    }
}
