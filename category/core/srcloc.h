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

#pragma once

typedef struct monad_source_location monad_source_location_t;

/// A C structure similar to C++20's std::source_location
struct monad_source_location
{
    char const *function_name;
    char const *file_name;
    unsigned line;
    unsigned column;
};

/// Creates a compound literal of the current source location for use in a
/// macro, similar to the C++20 consteval std::source_location::current()
#define MONAD_SOURCE_LOCATION_CURRENT()                                        \
    ((monad_source_location_t){__FUNCTION__, __FILE__, __LINE__, 0})
