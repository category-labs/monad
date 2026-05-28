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

#pragma once

// Throw a C++ exception
#define MONAD_THROW(exc, ...) throw exc(__VA_ARGS__)

// Wrap a try/catch pair. On platforms with exceptions disabled, these are
// redefined to erase the `try` keyword and reduce the `catch` to a dead
// `if constexpr (false)`, so the catch body still type-checks but never runs.
#define MONAD_TRY try
#define MONAD_CATCH(...) catch (__VA_ARGS__)
