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

#include "gtest/gtest.h"

#include <category/core/byte_string.hpp>
#include <category/core/hex.hpp>
#include <category/core/nibble.h>
#include <category/core/small_prng.hpp>
#include <category/mpt/nibbles_buffer.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <algorithm>
#include <cstdint>
#include <vector>

using namespace monad;
using namespace monad::mpt;
using namespace monad::literals;

namespace
{
    struct RandomViews
    {
        small_prng rng{0x62756666};
        byte_string buffer;

        RandomViews()
            : buffer(200, 0)
        {
            for (auto &b : buffer) {
                b = static_cast<unsigned char>(rng() | 0x11);
            }
        }

        NibblesView view(unsigned const max_size = 64)
        {
            unsigned const begin = rng() % 4;
            unsigned const size = rng() % (max_size + 1);
            return NibblesView{begin, begin + size, buffer.data()};
        }

        unsigned char nibble()
        {
            return static_cast<unsigned char>(rng() & 0xF);
        }
    };

    template <class... Args>
    void expect_matches_concat(Args const &...args)
    {
        NibblesBuffer const buffer{args...};
        EXPECT_EQ(NibblesView{buffer}, NibblesView{concat(args...)});
    }

    void expect_unused_nibbles_zero(NibblesBuffer const &buffer)
    {
        for (unsigned i = buffer.nibble_size(); i < 256; ++i) {
            EXPECT_EQ(get_nibble(buffer.data(), i), 0) << "nibble " << i;
        }
    }

    NibblesView
    model_view(std::vector<uint8_t> const &model, byte_string &bytes)
    {
        bytes.assign((model.size() + 1) / 2, 0);
        for (unsigned i = 0; i < model.size(); ++i) {
            set_nibble(bytes.data(), i, model[i]);
        }
        return NibblesView{
            0, static_cast<unsigned>(model.size()), bytes.data()};
    }
}

TEST(NibblesBufferTest, matches_concat)
{
    RandomViews in;
    for (unsigned iteration = 0; iteration < 20'000; ++iteration) {
        auto const a = in.view();
        auto const b = in.view();
        auto const c = in.view();
        auto const n = in.nibble();
        switch (iteration % 6) {
        case 0:
            expect_matches_concat(a);
            break;
        case 1:
            expect_matches_concat(a, b);
            break;
        case 2:
            expect_matches_concat(n, a);
            break;
        case 3:
            expect_matches_concat(a, n, b);
            break;
        case 4:
            expect_matches_concat(a, b, c);
            break;
        default: {
            Nibbles const prefix{a};
            expect_matches_concat(prefix, n, b);
        }
        }
        if (testing::Test::HasFailure()) {
            FAIL() << "iteration " << iteration;
        }
    }
}

TEST(NibblesBufferTest, unused_nibbles_stay_zero)
{
    RandomViews in;
    NibblesBuffer buffer;
    std::vector<uint8_t> model;
    byte_string model_bytes;
    for (unsigned step = 0; step < 10'000; ++step) {
        unsigned const room = 255 - buffer.nibble_size();
        switch (in.rng() % 3) {
        case 0:
            if (room > 0) {
                auto const n = in.nibble();
                buffer.push_back(n);
                model.push_back(n);
            }
            break;
        case 1: {
            auto const view = in.view(std::min(room, 64u));
            buffer.append(view);
            for (unsigned i = 0; i < view.nibble_size(); ++i) {
                model.push_back(view.get(i));
            }
            break;
        }
        default: {
            unsigned const size = in.rng() % (buffer.nibble_size() + 1);
            buffer.shrink(size);
            model.resize(size);
        }
        }
        ASSERT_EQ(buffer.nibble_size(), model.size());
        expect_unused_nibbles_zero(buffer);
        EXPECT_EQ(NibblesView{buffer}, model_view(model, model_bytes));
        if (testing::Test::HasFailure()) {
            FAIL() << "step " << step;
        }
    }
}

TEST(NibblesBufferTest, append_after_odd_shrink)
{
    NibblesBuffer b{NibblesView{0xABCDEF_bytes}};
    b.shrink(3);
    b.append(NibblesView{0x12_bytes});
    auto const expected = 0xABC120_bytes;
    EXPECT_EQ(NibblesView{b}, NibblesView{expected}.substr(0, 5));
    expect_unused_nibbles_zero(b);
}

TEST(NibblesBufferTest, holds_255_nibbles)
{
    byte_string const bytes(127, 0x5c);
    NibblesBuffer b{NibblesView{0, 254, bytes.data()}};
    b.push_back(0xA);
    EXPECT_EQ(b.nibble_size(), 255);
    EXPECT_EQ(b.get(254), 0xA);
}

TEST(NibblesBufferDeathTest, overflow_asserts)
{
    byte_string const bytes(127, 0x5c);
    NibblesBuffer b{NibblesView{0, 254, bytes.data()}};
    b.push_back(0xA);
    EXPECT_DEATH(b.push_back(0xB), "");
    EXPECT_DEATH(b.append(NibblesView{0, 1, bytes.data()}), "");
}

TEST(NibblesBufferTest, empty_views)
{
    NibblesBuffer const b{
        NibblesView{}, static_cast<unsigned char>(1), NibblesView{}};
    EXPECT_EQ(b.nibble_size(), 1);
    EXPECT_EQ(b.get(0), 1);
    EXPECT_TRUE(NibblesView{NibblesBuffer{}}.empty());
    EXPECT_TRUE(NibblesBuffer{}.empty());
}
