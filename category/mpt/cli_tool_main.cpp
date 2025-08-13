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

#include "cli_tool_impl.hpp"

#include <cstddef>
#include <iostream>
#include <string_view>
#include <vector>

int main(int argc_, char const *argv[])
{
    size_t const argc = size_t(argc_);
    std::vector<std::string_view> args(argc);
    for (size_t n = 0; n < argc; n++) {
        args[n] = argv[n];
    }
    return main_impl(std::cout, std::cerr, args);
}
