// Copyright (C) 2025 Category Labs, Inc.
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

#include "gtest/gtest.h"

#include <category/core/byte_string.hpp>
#include <category/core/hex.hpp>
#include <category/core/nibble.h>
#include <category/core/small_prng.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <algorithm>
#include <compare>
#include <cstring>
#include <variant>
#include <vector>

using namespace monad;
using namespace monad::mpt;
using namespace monad::literals;

namespace
{
    template <class... A>
    concept CanConcat = requires(A const &...a) { concat(a...); };

    using Piece = std::variant<unsigned char, NibblesView>;

    // The nibble-at-a-time concat that the bytewise one must match.
    Nibbles reference_concat(std::vector<Piece> const &pieces)
    {
        unsigned total = 0;
        for (auto const &piece : pieces) {
            total += std::holds_alternative<unsigned char>(piece)
                         ? 1u
                         : std::get<NibblesView>(piece).nibble_size();
        }
        Nibbles ret{total};
        unsigned index = 0;
        for (auto const &piece : pieces) {
            if (auto const *const nibble = std::get_if<unsigned char>(&piece)) {
                ret.set(index++, *nibble);
                continue;
            }
            auto const view = std::get<NibblesView>(piece);
            for (unsigned i = 0; i < view.nibble_size(); ++i) {
                ret.set(index++, view.get(i));
            }
        }
        return ret;
    }

    void expect_same_bytes(Nibbles const &result, Nibbles const &expected)
    {
        EXPECT_EQ(result.nibble_size(), expected.nibble_size());
        EXPECT_FALSE(result.begin_nibble());
        ASSERT_EQ(result.data_size(), expected.data_size());
        EXPECT_EQ(
            0,
            std::memcmp(result.data(), expected.data(), expected.data_size()));
    }

    struct RandomViews
    {
        small_prng rng{0x636f6e63};
        byte_string buffer;

        RandomViews()
            : buffer(200, 0)
        {
            for (auto &b : buffer) {
                b = static_cast<unsigned char>(rng() | 0x11);
            }
        }

        NibblesView view()
        {
            unsigned const begin = rng() % 4;
            unsigned const size = rng() % 65;
            return NibblesView{begin, begin + size, buffer.data()};
        }

        unsigned char nibble()
        {
            return static_cast<unsigned char>(rng() & 0xF);
        }
    };

    // The nibble-at-a-time comparisons that the bytewise ones must match.
    bool reference_equal(NibblesView const a, NibblesView const b)
    {
        if (a.nibble_size() != b.nibble_size()) {
            return false;
        }
        for (unsigned i = 0; i < a.nibble_size(); ++i) {
            if (a.get(i) != b.get(i)) {
                return false;
            }
        }
        return true;
    }

    std::strong_ordering
    reference_compare(NibblesView const a, NibblesView const b)
    {
        unsigned const min_size = std::min(a.nibble_size(), b.nibble_size());
        for (unsigned i = 0; i < min_size; ++i) {
            if (a.get(i) != b.get(i)) {
                return a.get(i) <=> b.get(i);
            }
        }
        return a.nibble_size() <=> b.nibble_size();
    }
}

TEST(NibblesViewTest, nibbles_view)
{
    auto const path =
        0x1234567812345678123456781234567812345678123456781234567812345678_bytes;

    NibblesView const a{12, 12, path.data()};
    EXPECT_EQ(a.data_size(), 0);
    EXPECT_EQ(a, NibblesView{});

    NibblesView const b{12, 16, path.data()};
    NibblesView const c{20, 24, path.data()};
    EXPECT_EQ(b, c);

    NibblesView const d{15, 18, path.data()};
    auto const expected_bytes = 0x8120_bytes;
    auto const expected = NibblesView{0, 3, expected_bytes.data()};
    EXPECT_EQ(d, expected);
}

TEST(NibblesViewTest, compare_matches_reference)
{
    small_prng rng{0x636d7072};
    unsigned char buf_a[34];
    unsigned char buf_b[34];
    for (unsigned iteration = 0; iteration < 50'000; ++iteration) {
        for (unsigned i = 0; i < sizeof(buf_a); ++i) {
            buf_a[i] = static_cast<unsigned char>(rng());
            buf_b[i] = static_cast<unsigned char>(rng());
        }
        unsigned const begin_a = rng() % 2;
        unsigned const begin_b = (rng() >> 4) % 2;
        unsigned const size_a = rng() % 65;
        bool const identical = iteration % 2 == 0;
        unsigned const size_b = identical ? size_a : rng() % 65;
        unsigned const min_size = std::min(size_a, size_b);
        unsigned const shared = identical ? min_size : rng() % (min_size + 1);
        for (unsigned i = 0; i < shared; ++i) {
            set_nibble(buf_b, begin_b + i, get_nibble(buf_a, begin_a + i));
        }
        NibblesView const a{begin_a, begin_a + size_a, buf_a};
        NibblesView const b{begin_b, begin_b + size_b, buf_b};
        EXPECT_EQ(a <=> b, reference_compare(a, b));
        EXPECT_EQ(a == b, reference_equal(a, b));
        if (testing::Test::HasFailure()) {
            FAIL() << "iteration " << iteration;
        }
    }
}

TEST(NibblesViewTest, compare_ignores_neighbour_half_bytes)
{
    // Nibbles 1..5 are equal; nibbles 0 and 6 differ.
    auto const left = 0x12345678_bytes;
    auto const right = 0x9234569f_bytes;
    NibblesView const a{1, 6, left.data()};
    NibblesView const b{1, 6, right.data()};
    EXPECT_EQ(a, b);
    EXPECT_EQ(a <=> b, std::strong_ordering::equal);

    // Nibbles 0..4 are equal; nibble 5, which shares a byte with nibble 4,
    // differs.
    NibblesView const c{0, 5, left.data()};
    auto const right_tail = 0x12345f_bytes;
    NibblesView const e{0, 5, right_tail.data()};
    EXPECT_EQ(c, e);
    EXPECT_EQ(c <=> e, std::strong_ordering::equal);
}

TEST(NibblesTest, concat_nibbles)
{
    auto path =
        0x1234567812345678123456781234567812345678123456781234567812345678_bytes;

    Nibbles const a =
        concat(get_nibble(path.data(), 0), NibblesView{1, 12, path.data()});
    EXPECT_EQ(a, (NibblesView{0, 12, path.data()}));

    Nibbles const b = concat(
        NibblesView{12, 16, path.data()},
        get_nibble(path.data(), 16),
        NibblesView{17, 20, path.data()});
    EXPECT_EQ(b, (NibblesView{12, 20, path.data()}));
}

TEST(NibblesTest, concat_rejects_non_nibble_arguments)
{
    static_assert(!CanConcat<int, NibblesView>);
    static_assert(!CanConcat<NibblesView, int, NibblesView>);
    static_assert(CanConcat<Nibbles, unsigned char, NibblesView>);
}

TEST(NibblesTest, concat_matches_reference)
{
    RandomViews in;
    for (unsigned iteration = 0; iteration < 20'000; ++iteration) {
        auto const a = in.view();
        auto const b = in.view();
        auto const c = in.view();
        auto const n = in.nibble();
        switch (iteration % 6) {
        case 0:
            expect_same_bytes(concat(a), reference_concat({a}));
            break;
        case 1:
            expect_same_bytes(concat(a, b), reference_concat({a, b}));
            break;
        case 2:
            expect_same_bytes(concat(n, a), reference_concat({n, a}));
            break;
        case 3:
            expect_same_bytes(concat(a, n, b), reference_concat({a, n, b}));
            break;
        case 4:
            expect_same_bytes(concat(a, b, c), reference_concat({a, b, c}));
            break;
        default: {
            Nibbles const prefix{a};
            expect_same_bytes(
                concat(prefix, n, b),
                reference_concat({NibblesView{prefix}, n, b}));
        }
        }
        if (testing::Test::HasFailure()) {
            FAIL() << "iteration " << iteration;
        }
    }
}

TEST(NibblesTest, concat_255_nibbles)
{
    byte_string bytes(127, 0x5c);
    NibblesView const view254{0, 254, bytes.data()};
    auto const result = concat(view254, static_cast<unsigned char>(0xA));
    EXPECT_EQ(result.nibble_size(), 255);
    expect_same_bytes(
        result, reference_concat({view254, static_cast<unsigned char>(0xA)}));
}

TEST(NibblesTest, concat_empty_views)
{
    EXPECT_EQ(concat(NibblesView{}, NibblesView{}).nibble_size(), 0);
    EXPECT_EQ(
        concat(NibblesView{}, static_cast<unsigned char>(3), NibblesView{}),
        concat(static_cast<unsigned char>(3)));
}

TEST(NibblesTest, copy_nibbles_preserves_leading_half_byte)
{
    unsigned char dest[3] = {0xB0, 0xFF, 0xFF};
    auto const src = 0x12_bytes;
    copy_nibbles(dest, 1, NibblesView{0, 2, src.data()});
    EXPECT_EQ(dest[0], 0xB1);
    EXPECT_EQ(dest[1], 0x20);
    EXPECT_EQ(dest[2], 0xFF);
}

TEST(NibblesTest, nibbles_size)
{
    Nibbles const nibbles{16};
    EXPECT_EQ(nibbles.nibble_size(), 16);
}

TEST(NibblesTest, substr_also_aligns)
{
    Nibbles const path{0x1234567812345678_bytes};

    ASSERT_EQ(path.nibble_size(), 16);

    Nibbles const a = path.substr(12);
    EXPECT_EQ(a.data_size(), 2);

    Nibbles const b = path.substr(1, 4);
    EXPECT_EQ(b.data_size(), 2);
}
