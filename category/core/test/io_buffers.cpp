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

#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>

#include <category/core/config.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

TEST(HugeMem, works)
{
    using namespace MONAD_NAMESPACE;
    {
        io::Ring ring;
        io::Buffers const buffers = io::make_buffers_for_read_only(ring, 8);
    }
    {
        io::Ring ring;
        io::Buffers const buffers =
            io::make_buffers_for_mixed_read_write(ring, 8, 8);
    }
    {
        io::Ring ring1;
        io::Ring ring2;
        io::Buffers const buffers =
            io::make_buffers_for_segregated_read_write(ring1, ring2, 8, 8);
    }
}
