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
#include <category/core/nibble.h>
#include <category/mpt/nibbles_view.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

using namespace monad::mpt;
using namespace monad::literals;

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
